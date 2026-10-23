#!/usr/bin/env python3
"""Verify import identities and tracked-file policy; no scientific acceptance.

BootLoops has no repository export verifier. This standard-library wrapper
checks file provenance without changing the original scientific instruments.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LIMIT = 1024 * 1024
SECRET_PATTERNS = [
    re.compile(rb'\b(?:gh[pousr]_[A-Za-z0-9]{30,255}|github_pat_[A-Za-z0-9_]{40,255})\b'),
    re.compile(rb'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----'),
    re.compile(rb'\bsk-(?:proj-|svcacct-)?[A-Za-z0-9_-]{40,255}\b'),
    re.compile(rb'\b(?:AKIA|ASIA)[A-Z0-9]{16}\b'),
]

def verify_row(root, row):
    path = root / row['path']
    if not path.is_file() or path.is_symlink():
        raise ValueError('Missing/nonregular imported file: ' + row['path'])
    data = path.read_bytes()
    if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
        raise ValueError('Imported bytes differ: ' + row['path'])

def controls():
    with tempfile.TemporaryDirectory() as folder:
        base = Path(folder)
        (base / 'fixture').write_bytes(b'known bytes\n')
        row = {'path':'fixture','bytes':12,'sha256':hashlib.sha256(b'known bytes\n').hexdigest()}
        verify_row(base, row)
        (base / 'fixture').write_bytes(b'wrong bytes\n')
        try:
            verify_row(base, row)
        except ValueError:
            return
        raise RuntimeError('Import comparator accepted a deliberately corrupted file')

def main():
    controls()
    summary = json.loads((ROOT / 'docs/import/snapshot.json').read_text())
    seen = set()
    total = 0
    for shard in sorted((ROOT / 'docs/import').glob('included-*.jsonl')):
        for line in shard.read_text().splitlines():
            row = json.loads(line)
            if row['path'] in seen:
                raise ValueError('Duplicate import record: ' + row['path'])
            seen.add(row['path'])
            verify_row(ROOT, row)
            total += row['bytes']
    if len(seen) != summary['included_files'] or total != summary['included_bytes']:
        raise ValueError('Manifest denominator or byte count differs from snapshot')
    if not seen:
        raise ValueError('Empty import cannot pass')
    paths = subprocess.check_output(['git','ls-files','-z'],cwd=ROOT).decode().split('\0')
    paths = [p for p in paths if p]
    if not paths:
        raise ValueError('No tracked files; stage the initial import before checking')
    largest = 0
    for name in paths:
        path = ROOT / name
        if path.is_symlink() or not path.is_file():
            raise ValueError('Tracked file is missing or a symlink: ' + name)
        size = path.stat().st_size
        largest = max(largest,size)
        if size > LIMIT:
            raise ValueError('Tracked file exceeds 1 MiB: ' + name)
        if path.suffix in {'.olean','.ilean','.pyc','.sqlite','.db'}:
            raise ValueError('Compiled/local file is tracked: ' + name)
        data = path.read_bytes()
        if any(pattern.search(data) for pattern in SECRET_PATTERNS):
            raise ValueError('Possible credential pattern in tracked file: ' + name)
    required=['README.md','AGENTS.md','CONTRIBUTING.md','autoresearch.md','LICENSE','NOTICE',
              'CONTRIBUTORS.md','CITATION.cff','.github/CODEOWNERS',
              '.github/workflows/verify.yml','certificates/selected-result.json']
    for name in required:
        if name not in paths:
            raise ValueError('Required collaboration file is not tracked: ' + name)
    result=json.loads((ROOT/'certificates/selected-result.json').read_text())
    if result['selected_complete_result'] is not None:
        raise ValueError('Initial import must not select an unreviewed complete result')
    print(json.dumps({'check':'repository-import-and-file-policy','status':'passed',
        'imported_files_checked':len(seen),'imported_bytes_checked':total,
        'tracked_files_checked':len(paths),'largest_tracked_file_bytes':largest,
        'corrupted_import_control':'rejected','scope':'Packaging and byte identity only; no scientific acceptance.'}))

if __name__ == '__main__': main()
