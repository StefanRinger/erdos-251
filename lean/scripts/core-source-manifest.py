#!/usr/bin/env python3
"""Static Lean source inventory; NOT kernel, freshness, coverage, or release acceptance.

The tool follows literal repository-local ``import`` commands from one or
more entry modules and hashes the resulting source files.  It never invokes
Lean/Lake, Git, the network, or package-cache traversal.
"""

from __future__ import annotations

import argparse
import hashlib
import heapq
import json
import os
from pathlib import Path
import re
import sys
from typing import Dict, Iterable, List, Optional, Set, Tuple


MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
IMPORT_RE = re.compile(r"^\s*import\b(.*)$")
EXTERNAL_ROOTS = frozenset({"Batteries", "Init", "Lake", "Lean", "Mathlib", "Std"})
METADATA_PATHS = (
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
    "lakefile.lean",
)
PNT_RECORD_PATHS = (
    "PrimeGapNormality/ClassicalPNT/LICENSE",
    "PrimeGapNormality/ClassicalPNT/PROVENANCE.md",
    "PrimeGapNormality/ClassicalPNT/CITATION.upstream.cff",
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def strip_comments_and_strings(text: str) -> Tuple[str, List[str]]:
    """Replace nested Lean comments and strings with spaces, preserving newlines."""

    output: List[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string:
            if char == "\\" and index + 1 < len(text):
                output.append(" ")
                next_char = text[index + 1]
                output.append("\n" if next_char == "\n" else " ")
                index += 2
            elif char == '"':
                in_string = False
                output.append(" ")
                index += 1
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif pair == "--":
            while index < len(text) and text[index] != "\n":
                output.append(" ")
                index += 1
        elif pair == "/-":
            block_depth = 1
            output.extend("  ")
            index += 2
        elif char == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1
    issues: List[str] = []
    if block_depth:
        issues.append("unterminated block comment")
    if in_string:
        issues.append("unterminated string literal")
    return "".join(output), issues


def literal_imports(path: Path) -> Tuple[List[str], List[Dict[str, object]]]:
    text = path.read_text(encoding="utf-8")
    stripped, lexical_issues = strip_comments_and_strings(text)
    imports: List[str] = []
    parse_issues: List[Dict[str, object]] = [
        {"line": text.count("\n") + 1, "reason": reason} for reason in lexical_issues
    ]
    for line_number, line in enumerate(stripped.splitlines(), 1):
        match = IMPORT_RE.match(line)
        if not match:
            continue
        tokens = match.group(1).split()
        if not tokens:
            parse_issues.append({"line": line_number, "reason": "empty import command"})
            continue
        for token in tokens:
            if MODULE_RE.fullmatch(token):
                imports.append(token)
            else:
                parse_issues.append(
                    {
                        "line": line_number,
                        "reason": "unsupported or ambiguous import token",
                        "token": token,
                    }
                )
    return imports, parse_issues


def module_relative_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def within_root(root: Path, path: Path) -> bool:
    try:
        common = os.path.commonpath((str(root), str(path)))
    except ValueError:
        return False
    return common == str(root)


def symlink_component(root: Path, relative: Path) -> Optional[str]:
    current = root
    for component in relative.parts:
        current = current / component
        if current.is_symlink():
            return current.relative_to(root).as_posix()
    return None


def hashed_optional(root: Path, relative: str) -> Tuple[Dict[str, object], Optional[Dict[str, str]]]:
    path = root / relative
    relative_path = Path(relative)
    link = symlink_component(root, relative_path)
    resolved = path.resolve(strict=False)
    if link is not None:
        reason = "symlink/path escape" if not within_root(root, resolved) else "symlink component"
        issue = {"path": relative, "reason": reason, "symlink": link}
        return {"path": relative, "status": "unsafe", "reason": reason, "symlink": link}, issue
    if not within_root(root, resolved):
        issue = {"path": relative, "reason": "path escape"}
        return {"path": relative, "status": "unsafe", "reason": "path escape"}, issue
    if path.is_file():
        return {"path": relative, "sha256": sha256_file(path), "status": "present"}, None
    return {"path": relative, "status": "missing"}, None


def project_topology(
    modules: Set[str], edges: Set[Tuple[str, str]]
) -> Tuple[List[str], List[Dict[str, object]]]:
    """Return a stable dependency-first order and explicit local import cycles."""

    dependencies: Dict[str, Set[str]] = {module: set() for module in modules}
    for consumer, dependency in edges:
        if consumer in modules and dependency in modules:
            dependencies[consumer].add(dependency)

    # Tarjan SCC traversal is sorted so cycle reports are byte-stable.
    index = 0
    indices: Dict[str, int] = {}
    lowlinks: Dict[str, int] = {}
    stack: List[str] = []
    on_stack: Set[str] = set()
    components: List[List[str]] = []

    def visit(module: str) -> None:
        nonlocal index
        indices[module] = index
        lowlinks[module] = index
        index += 1
        stack.append(module)
        on_stack.add(module)
        for dependency in sorted(dependencies[module]):
            if dependency not in indices:
                visit(dependency)
                lowlinks[module] = min(lowlinks[module], lowlinks[dependency])
            elif dependency in on_stack:
                lowlinks[module] = min(lowlinks[module], indices[dependency])
        if lowlinks[module] == indices[module]:
            component: List[str] = []
            while True:
                member = stack.pop()
                on_stack.remove(member)
                component.append(member)
                if member == module:
                    break
            components.append(sorted(component))

    for module in sorted(modules):
        if module not in indices:
            visit(module)

    cycles: List[Dict[str, object]] = []
    for component in components:
        component_set = set(component)
        if len(component) > 1 or any(module in dependencies[module] for module in component):
            cycle_edges = [
                {"from": consumer, "to": dependency}
                for consumer, dependency in sorted(edges)
                if consumer in component_set and dependency in component_set
            ]
            cycles.append({"modules": component, "edges": cycle_edges})
    cycles.sort(key=lambda item: tuple(item["modules"]))
    if cycles:
        return [], cycles

    # Edges are importer -> dependency, so this indegree is the number of
    # validated local dependencies still needing to precede each consumer.
    remaining_dependencies = {module: len(dependencies[module]) for module in modules}
    consumers: Dict[str, Set[str]] = {module: set() for module in modules}
    for consumer, module_dependencies in dependencies.items():
        for dependency in module_dependencies:
            consumers[dependency].add(consumer)
    ready = [module for module, count in remaining_dependencies.items() if count == 0]
    heapq.heapify(ready)
    order: List[str] = []
    while ready:
        dependency = heapq.heappop(ready)
        order.append(dependency)
        for consumer in sorted(consumers[dependency]):
            remaining_dependencies[consumer] -= 1
            if remaining_dependencies[consumer] == 0:
                heapq.heappush(ready, consumer)
    return order, []


def build_manifest(root: Path, entries: Iterable[str]) -> Tuple[Dict[str, object], bool]:
    root = root.resolve()
    entry_names = sorted(set(entries))
    local_roots: Set[str] = {entry.split(".", 1)[0] for entry in entry_names}
    local_roots.update({"PrimeGapNormality", "PrimeNumberTheoremAnd"})

    pending = list(reversed(entry_names))
    queued: Set[str] = set(entry_names)
    imported_from: Dict[str, str] = {entry: "<entry>" for entry in entry_names}
    visited: Set[str] = set()
    source_modules: Set[str] = set()
    source_paths: Set[str] = set()
    local_edges: Set[Tuple[str, str]] = set()
    external_by_module: Dict[str, Set[str]] = {}
    missing_local: List[Dict[str, str]] = []
    ambiguous: List[Dict[str, str]] = []
    path_issues: List[Dict[str, str]] = []
    parse_issues: List[Dict[str, object]] = []

    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        importer = imported_from[module]

        if not MODULE_RE.fullmatch(module):
            ambiguous.append({"imported_by": importer, "module": module})
            continue
        relative_text = module_relative_path(module)
        relative = Path(relative_text)
        candidate = root / relative
        link = symlink_component(root, relative)
        resolved = candidate.resolve(strict=False)
        if link is not None:
            issue = {"module": module, "path": relative_text, "reason": "symlink component", "symlink": link}
            if not within_root(root, resolved):
                issue["reason"] = "symlink/path escape"
            path_issues.append(issue)
            continue
        if not within_root(root, resolved):
            path_issues.append({"module": module, "path": relative_text, "reason": "path escape"})
            continue
        if not candidate.is_file():
            missing_local.append({"imported_by": importer, "module": module, "path": relative_text})
            continue

        source_paths.add(relative_text)
        source_modules.add(module)
        imports, issues = literal_imports(candidate)
        for issue in issues:
            parse_issues.append({"path": relative_text, **issue})
        for dependency in imports:
            first = dependency.split(".", 1)[0]
            dependency_path = root / module_relative_path(dependency)
            if dependency_path.exists() or dependency_path.is_symlink() or first in local_roots:
                local_edges.add((module, dependency))
                if dependency not in queued:
                    queued.add(dependency)
                    imported_from[dependency] = module
                    pending.append(dependency)
            elif first in EXTERNAL_ROOTS:
                external_by_module.setdefault(dependency, set()).add(module)
            else:
                ambiguous.append({"imported_by": module, "module": dependency})

    sources = [
        {"path": relative, "sha256": sha256_file(root / relative)}
        for relative in sorted(source_paths)
    ]
    external = [
        {"module": module, "imported_by": sorted(importers)}
        for module, importers in sorted(external_by_module.items())
    ]
    project_build_order, import_cycles = project_topology(source_modules, local_edges)
    metadata_records: List[Dict[str, object]] = []
    pnt_records: List[Dict[str, object]] = []
    metadata_path_issues: List[Dict[str, str]] = []
    for relative in METADATA_PATHS:
        record, issue = hashed_optional(root, relative)
        metadata_records.append(record)
        if issue is not None:
            metadata_path_issues.append(issue)
    for relative in PNT_RECORD_PATHS:
        record, issue = hashed_optional(root, relative)
        pnt_records.append(record)
        if issue is not None:
            metadata_path_issues.append(issue)

    manifest: Dict[str, object] = {
        "schema_version": 2,
        "inventory_kind": "static-source-only",
        "disclaimer": "NOT kernel, freshness, mathematical coverage, or release acceptance",
        "parser_scope": "literal Lean import commands after nested-comment/string stripping; not a full Lean parser",
        "entries": entry_names,
        "sources": sources,
        "local_import_edges": [
            {"from": source, "to": target} for source, target in sorted(local_edges)
        ],
        "project_build_order": project_build_order,
        "project_build_order_scope": (
            "validated repository-local modules only; dependencies precede consumers; "
            "external imports are excluded and their cache must be prepared separately"
        ),
        "import_cycles": import_cycles,
        "external_imports": external,
        "missing_local_imports": sorted(missing_local, key=lambda item: (item["module"], item["imported_by"])),
        "ambiguous_imports": sorted(ambiguous, key=lambda item: (item["module"], item["imported_by"])),
        "path_issues": sorted(path_issues, key=lambda item: (item["module"], item["path"])),
        "metadata_path_issues": sorted(metadata_path_issues, key=lambda item: item["path"]),
        "parse_issues": sorted(parse_issues, key=lambda item: (str(item["path"]), int(item["line"]))),
        "project_metadata": metadata_records,
        "pnt_license_provenance": pnt_records,
    }
    failed = bool(
        missing_local or ambiguous or path_issues or metadata_path_issues or parse_issues or import_cycles
    )
    return manifest, failed


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--entry", action="append", required=True, help="Lean module entry; repeat for multiple entries")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent, help=argparse.SUPPRESS)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    manifest, failed = build_manifest(args.root, args.entry)
    json.dump(manifest, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 2 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
