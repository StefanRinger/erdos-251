#!/usr/bin/env python3
"""Static command-level Lean trust inventory; NOT kernel or semantic acceptance.

The scanner reuses ``core-source-manifest.py`` for literal repository-local
import closure, hashing, and path validation.  It scans only validated project
sources after the same nested-comment/string stripping.  It never invokes
Lean, Lake, Git, the network, or a package cache.

This is deliberately not a full Lean parser.  A clean result cannot certify
types, theorem assumptions, source freshness, kernel checking, mathematical
coverage, or permission to release.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys
from types import ModuleType
from typing import Dict, Iterable, List, Tuple


MANIFEST_SCRIPT = Path(__file__).resolve().with_name("core-source-manifest.py")

# This list classifies options already used by the project.  It is not Lean's
# option registry, and an unlisted name is reported for review rather than
# declared invalid.
KNOWN_PROJECT_OPTIONS = frozenset(
    {
        "backward.isDefEq.respectTransparency",
        "lang.lemmaCmd",
        "linter.dupNamespace",
        "linter.style.header",
        "linter.unnecessarySimpa",
        "linter.unusedSimpArgs",
        "linter.unusedTactic",
        "linter.unusedVariables",
        "maxHeartbeats",
        "pp.universes",
        "synthInstance.maxHeartbeats",
    }
)

# These names require explicit trust review if encountered.  The list is
# conservative and intentionally small; unknown names are also surfaced.
TRUST_SENSITIVE_OPTIONS = frozenset(
    {
        "debug.skipKernelTC",
        "compiler.ignoreExtern",
    }
)

SET_OPTION_RE = re.compile(r"\bset_option\s+([A-Za-z_][A-Za-z0-9_.]*)\b")
AXIOM_COMMAND_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\]\s*)*"
    r"(?:(?:private|protected|public|noncomputable)\s+)*(axioms?)\b"
)
HASH_COMMAND_RE = re.compile(r"^[ \t]*(#\s*(?:eval|reduce))\b")
TOKEN_PATTERNS: Tuple[Tuple[str, re.Pattern[str]], ...] = tuple(
    (kind, re.compile(rf"(?<![A-Za-z0-9_'])({re.escape(token)})(?![A-Za-z0-9_'])"))
    for kind, token in (
        ("placeholder", "sorry"),
        ("placeholder", "admit"),
        ("trust_constant", "sorryAx"),
        ("trust_constant", "admitAx"),
        ("trust_constant", "syntheticOpaque"),
        ("trust_constant", "ofReduceBool"),
        ("unsafe_token", "unsafe"),
        ("extern_token", "extern"),
        ("implemented_by", "implemented_by"),
        ("native_decide", "native_decide"),
    )
)


def load_manifest_module() -> ModuleType:
    spec = importlib.util.spec_from_file_location("core_source_manifest", MANIFEST_SCRIPT)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load core-source-manifest.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def code_preview(line: str) -> str:
    return " ".join(line.strip().split())[:240]


def occurrence(path: str, line_number: int, column: int, kind: str, token: str,
               line: str) -> Dict[str, object]:
    return {
        "path": path,
        "line": line_number,
        "column": column,
        "kind": kind,
        "token": token,
        "code": code_preview(line),
    }


def scan_source(path: str, text: str, manifest_module: ModuleType) -> Tuple[List[Dict[str, object]], List[Dict[str, object]]]:
    stripped, _ = manifest_module.strip_comments_and_strings(text)
    risky: List[Dict[str, object]] = []
    options: List[Dict[str, object]] = []
    for line_number, line in enumerate(stripped.splitlines(), 1):
        axiom_match = AXIOM_COMMAND_RE.match(line)
        if axiom_match:
            risky.append(occurrence(path, line_number, axiom_match.start(1) + 1,
                                    "axiom_command", axiom_match.group(1), line))

        hash_match = HASH_COMMAND_RE.match(line)
        if hash_match:
            token = re.sub(r"\s+", "", hash_match.group(1))
            risky.append(occurrence(path, line_number, hash_match.start(1) + 1,
                                    "evaluation_command", token, line))

        for kind, pattern in TOKEN_PATTERNS:
            for match in pattern.finditer(line):
                risky.append(occurrence(path, line_number, match.start(1) + 1,
                                        kind, match.group(1), line))

        for match in SET_OPTION_RE.finditer(line):
            name = match.group(1)
            if name in TRUST_SENSITIVE_OPTIONS:
                classification = "trust-sensitive"
            elif name in KNOWN_PROJECT_OPTIONS:
                classification = "known-project-option"
            else:
                classification = "unknown-to-static-allowlist"
            options.append(
                {
                    "path": path,
                    "line": line_number,
                    "column": match.start(1) + 1,
                    "name": name,
                    "classification": classification,
                }
            )
    return risky, options


def build_trust_inventory(root: Path, entries: Iterable[str]) -> Tuple[Dict[str, object], int]:
    manifest_module = load_manifest_module()
    manifest, closure_failed = manifest_module.build_manifest(root, entries)
    resolved_root = root.resolve()
    risky: List[Dict[str, object]] = []
    options: List[Dict[str, object]] = []

    # build_manifest includes only validated, non-symlink project source paths.
    for source in manifest["sources"]:
        relative = source["path"]
        text = (resolved_root / relative).read_text(encoding="utf-8")
        source_risky, source_options = scan_source(relative, text, manifest_module)
        risky.extend(source_risky)
        options.extend(source_options)

    risky.sort(key=lambda item: (str(item["path"]), int(item["line"]), int(item["column"]), str(item["kind"])))
    options.sort(key=lambda item: (str(item["path"]), int(item["line"]), int(item["column"])))
    unknown_options = [item for item in options if item["classification"] == "unknown-to-static-allowlist"]
    trust_options = [item for item in options if item["classification"] == "trust-sensitive"]

    closure_issues = {
        "import_cycles": manifest["import_cycles"],
        "missing_local_imports": manifest["missing_local_imports"],
        "ambiguous_imports": manifest["ambiguous_imports"],
        "path_issues": manifest["path_issues"],
        "metadata_path_issues": manifest["metadata_path_issues"],
        "parse_issues": manifest["parse_issues"],
    }
    inventory: Dict[str, object] = {
        "schema_version": 1,
        "inventory_kind": "static-command-level-trust-scan",
        "disclaimer": "NOT kernel, type, freshness, semantic-assumption, mathematical-coverage, or release acceptance",
        "parser_scope": "validated local literal-import closure; nested comments and strings stripped; not a full Lean parser",
        "entries": manifest["entries"],
        "sources": manifest["sources"],
        "external_imports": manifest["external_imports"],
        "closure_issues": closure_issues,
        "risky_occurrences": risky,
        "set_option_occurrences": options,
        "unknown_option_occurrences": unknown_options,
        "trust_sensitive_option_occurrences": trust_options,
        "option_classification_basis": "small project-observed allowlist, not the Lean option registry",
        "exit_status_meaning": {
            "0": "no static risky occurrence, unknown option, trust-sensitive option, or closure issue",
            "1": "static risky occurrence or option requiring review",
            "2": "manifest closure, import/cycle, path, metadata-path, or lexical issue",
        },
    }
    if closure_failed:
        return inventory, 2
    if risky or unknown_options or trust_options:
        return inventory, 1
    return inventory, 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--entry", action="append", required=True,
                        help="Lean module entry; repeat for multiple entries")
    parser.add_argument("--root", type=Path,
                        default=Path(__file__).resolve().parent.parent,
                        help=argparse.SUPPRESS)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    inventory, exit_code = build_trust_inventory(args.root, args.entry)
    json.dump(inventory, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
