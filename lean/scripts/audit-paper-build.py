#!/usr/bin/env python3
"""Capture genuine build traces and all requested transitive axiom outputs.

Run after the full build and freshness check. Not a substitute for mathematical
statement review or independent-kernel verification. No Lean is invoked here.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
ENTRIES = ['PrimeGapNormality.Paper', 'PrimeGapNormality.PaperAudit']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_checks(messages):
    checks = []
    for message in messages:
        for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", message):
            axioms = {re.sub(r'\.\{[^{}]*\}$', '', a.strip())
                      for a in m[2].split(',') if a.strip()}
            if not axioms <= STANDARD:
                raise ValueError(f'Unexpected axioms for {m[1]}: {axioms}')
            checks.append({'theorem': m[1], 'axioms': sorted(axioms)})
        for m in re.finditer(r"'([^']+)' does not depend on any axioms", message):
            checks.append({'theorem': m[1], 'axioms': []})
    return checks


def validate_names(expected, actual):
    remaining = Counter(c['theorem'] for c in actual)
    for name in expected:
        candidates = [n for n, count in remaining.items() if count and
                      (n == name or n.endswith('.' + name))]
        if len(candidates) != 1:
            raise ValueError(f'Missing or ambiguous axiom output for {name}: {candidates}')
        remaining[candidates[0]] -= 1
    if any(remaining.values()):
        raise ValueError(f'Unmatched axiom output: {remaining}')


def inventory(script):
    command = [sys.executable, str(ROOT / 'scripts' / script)]
    for entry in ENTRIES:
        command.extend(['--entry', entry])
    return json.loads(subprocess.check_output(command, cwd=ROOT, text=True))


def capture(build_report):
    if (build_report / 'build_exit.txt').read_text().strip() != '0':
        raise ValueError('Successful build exit is missing')
    if not (build_report / 'finished_utc.txt').is_file():
        raise ValueError('Build/freshness/source checks did not complete')
    if 'up-to-date' not in (build_report / 'freshness.txt').read_text():
        raise ValueError('Successful freshness output missing')
    manifest = inventory('core-source-manifest.py')
    trust = inventory('core-trust-scan.py')
    if manifest != json.loads((build_report / 'source_after.json').read_text()):
        raise ValueError('Sources or dependency metadata changed after the build')
    if trust['sources'] != manifest['sources']:
        raise ValueError('Source drift during static trust scan')
    baseline = json.loads((ROOT / 'verification/core-source-manifest.json').read_text())
    if baseline != manifest:
        raise ValueError('Unreviewed delta from the public source inventory')
    spec = importlib.util.spec_from_file_location('inventory', ROOT / 'scripts/core-source-manifest.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    artifacts, all_checks, audit_text = [], [], []
    for source in manifest['sources']:
        rel = Path(source['path'])
        path = ROOT / rel
        trace_path = (ROOT / '.lake/build/lib/lean' / rel).with_suffix('.trace')
        olean_path = trace_path.with_suffix('.olean')
        trace = json.loads(trace_path.read_text())
        if trace.get('synthetic') is not False or not olean_path.is_file():
            raise ValueError(f'No genuine artifact for {rel}')
        if trace_path.stat().st_mtime_ns < path.stat().st_mtime_ns:
            raise ValueError(f'Outdated trace for {rel}')
        if sha(path) != source['sha256']:
            raise ValueError(f'Source changed: {rel}')
        logs = trace.get('log', [])
        if any(item.get('level') == 'error' for item in logs):
            raise ValueError(f'Compiler errors: {rel}')
        messages = [item.get('message', '') for item in logs if item.get('level') != 'trace']
        if any('sorryAx' in m or "declaration uses 'sorry'" in m for m in messages):
            raise ValueError(f'Untrusted proof: {rel}')
        code, _ = module.strip_comments_and_strings(path.read_text())
        expected = re.findall(r'^\s*#print\s+axioms\s+([A-Za-z0-9_.]+)', code, re.M)
        checks = read_checks(messages)
        validate_names(expected, checks)
        for check in checks:
            all_checks.append({'module': rel.with_suffix('').as_posix().replace('/', '.'), **check})
        if expected:
            audit_text.append('\n=== ' + rel.as_posix() + ' ===\n' + '\n'.join(messages))
        artifacts.append({'source': rel.as_posix(), 'source_sha256': source['sha256'],
                          'trace_sha256': sha(trace_path), 'olean_sha256': sha(olean_path)})
    if not all_checks:
        raise ValueError('Empty axiom audit')
    binding = json.loads((ROOT / 'verification/paper-binding.json').read_text())
    for name, digest in binding['sha256'].items():
        if sha(ROOT.parent / 'paper' / name) != digest:
            raise ValueError(f'Paper changed: {name}')
    # Recheck inventory after reading artifacts; no automatic acceptance on drift.
    if inventory('core-source-manifest.py') != manifest:
        raise ValueError('Sources changed during artifact inspection')
    return {'status': 'PASS: local build and requested transitive axiom outputs',
            'limits': 'Not an independent clean-machine rebuild or a mathematical statement review',
            'entries': ENTRIES, 'paper_sha256': binding['sha256'],
            'started_utc': (build_report / 'started_utc.txt').read_text().strip(),
            'finished_utc': (build_report / 'finished_utc.txt').read_text().strip(),
            'build_log_sha256': sha(build_report / 'build.txt'),
            'source_manifest_sha256': sha(build_report / 'source_after.json'),
            'artifacts': artifacts, 'axiom_checks': all_checks}, '\n'.join(audit_text)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('build_report', type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit('Refusing to overwrite an existing acceptance directory')
    evidence, text = capture(args.build_report.resolve())
    args.output.mkdir(parents=True)
    (args.output / 'build-and-axioms.json').write_text(json.dumps(evidence, indent=2) + '\n')
    (args.output / 'theorem-types-and-axioms.txt').write_text(text + '\n')
    print(f"PASS: {len(evidence['artifacts'])} genuine source/artifact bindings; "
          f"{len(evidence['axiom_checks'])} requested axiom checks.")
