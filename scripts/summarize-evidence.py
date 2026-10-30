#!/usr/bin/env python3
"""Render COMPLETED local evidence; incomplete or failed evidence exits nonzero.
Usage: summarize-evidence.py EVIDENCE_DIR [BUILD_LOG] [PROBES_LOG]
The old committed summary remains historical evidence. New runs require the
structured completion markers produced by verification.py; a log's presence
alone is not success, and a build log does not prove empty-cache rebuilding.
"""
import json
import hashlib
from pathlib import Path
import re
import sys

INTERFACES = ('heights', 'locallimits', 'samelaw', 'sir')
KERNELS = ('leanchecker', 'nanoda', 'leanchecker-paranoid', 'lean4lean', 'con-leche', 'con-ron')


def complete(path, mode):
    data = json.loads(path.read_text())
    if data.get('mode') != mode or data.get('status') != 'passed' or data.get('exit_code') != 0:
        raise ValueError(f'No successful completion marker: {path}')
    return data


def statuses(path, expected):
    entries = re.findall(r'^(.+) exit=(\d+)$', path.read_text(), re.M)
    if len(entries) != len(expected) or {n for n, _ in entries} != set(expected) or any(c != '0' for _, c in entries):
        raise ValueError(f'Failed, missing or duplicate command statuses: {path}')


def sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def main():
    if len(sys.argv) not in (2, 3, 4):
        raise ValueError('usage: EVIDENCE_DIR [BUILD_LOG] [PROBES_LOG]')
    out = Path(sys.argv[1])
    result = complete(out / 'result.json', 'collect')
    ident = json.loads((out / 'identity.json').read_text())
    if ident.get('git_status') != 'clean' or ident.get('verified_unchanged_at_end') is not True or any(not re.fullmatch('[0-9a-f]{40}', ident.get(field, '')) for field in ('commit', 'tree')):
        raise ValueError('Evidence has no clean, identified source commit')
    if not all(isinstance(ident.get(field), str) and ident[field] for field in ('toolchain', 'platform')) or not re.fullmatch(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z', result.get('completed_utc', '')):
        raise ValueError('Incomplete evidence identity/completion metadata')
    expected = ['build', 'source-scan', 'axiom-audit', 'main-results-axioms', 'check-axiom-log']
    expected += [step for cfg in INTERFACES for step in (f'{cfg} diagnostic', f'{cfg} replays')]
    expected += ['auxiliary diagnostic']
    statuses(out / 'evidence.log', expected)
    rows = []
    for cfg in (*INTERFACES, 'auxiliary'):
        base = out / cfg
        compared = complete(base / 'result.json', 'compare')
        if not re.fullmatch('[0-9a-f]{64}', compared.get('config_sha256', '')):
            raise ValueError(f'Missing configuration digest for {cfg}')
        for side in ('challenge', 'solution'):
            digest = sha256(base / f'{side}.ndjson')
            if compared.get(f'{side}_sha256') != digest:
                raise ValueError(f'{cfg} {side} export no longer matches its comparison record')
        statuses(base / 'run.log', ['export challenge', 'export solution', 'compile diagnostic', 'link diagnostic', 'comparison', 'leanchecker'])
        compare = (base / 'compare.log').read_text()
        if 'statements and reachable constants match' not in compare or 'only permitted axioms' not in compare:
            raise ValueError(f'Missing comparison confirmations for {cfg}')
        if cfg != 'auxiliary':
            replayed = complete(base / 'kernels/result.json', 'replay')
            if not re.fullmatch('[0-9a-f]{64}', replayed.get('config_sha256', '')):
                raise ValueError(f'Missing replay configuration digest for {cfg}')
            statuses(base / 'kernels/kernels.log', KERNELS)
            kernel_log = (base / 'kernels/kernels.log').read_text()
            match = re.search(r'^solution SHA-256: ([0-9a-f]{64})$', kernel_log, re.M)
            if not match:
                raise ValueError(f'Missing solution digest for {cfg}')
            digest = match.group(1)
            if digest != compared.get('solution_sha256') or digest != replayed.get('solution_sha256') or compared.get('config_sha256') != replayed.get('config_sha256'):
                raise ValueError(f'{cfg} comparison and kernel replay are not bound to the same export/config')
        else:
            digest = 'not replayed'
        rows.append((cfg, digest))
    build = Path(sys.argv[2]).read_text() if len(sys.argv) > 2 else (out / 'build.log').read_text()
    jobs = re.search(r'Build completed successfully \((\d+) jobs\)', build)
    if not jobs:
        raise ValueError('Build log has no success confirmation')
    probes = None
    if len(sys.argv) > 3:
        probes = [l for l in Path(sys.argv[3]).read_text().splitlines() if ' exit=' in l]
        if not probes or any(not l.endswith('exit=0') for l in probes):
            raise ValueError('Missing or failed probe statuses')
    # Print a passing summary only after every required item has been validated.
    print('# Local verification evidence\n')
    print('This is local unsandboxed comparison/replay, not the official Palomar mechanical report.\n')
    print(f"Source commit: `{ident['commit']}`; tree: `{ident['tree']}`; clean checkout.")
    print(f"Toolchain: `{ident['toolchain']}`; platform: `{ident['platform']}`.")
    print(f"Completed: {result['completed_utc']}.\n")
    print(f"Build: PASS ({jobs.group(1)} jobs). No empty-cache/clean-build claim is inferred from this log.")
    print('Source scan and both axiom audits: successful command exits.\n')
    print('| Interface | Comparison/axioms | Selected kernel replays | Solution SHA-256 |')
    print('| --- | --- | --- | --- |')
    for cfg, digest in rows:
        print(f"| {cfg} | match/permitted | {'all six exit 0' if cfg != 'auxiliary' else 'not run'} | `{digest}` |")
    print(f'\nProbes: {len(probes)} successful recorded checks.' if probes is not None else '\nNo separate probe log was supplied.')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as exc:
        print(f'ERROR: cannot certify this evidence: {exc}', file=sys.stderr)
        sys.exit(1)
