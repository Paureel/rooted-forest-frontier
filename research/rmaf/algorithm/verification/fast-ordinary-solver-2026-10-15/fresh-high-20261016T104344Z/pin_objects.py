#!/usr/bin/env python3
"""One-shot filtered pin verification, with no source text disclosure."""
import hashlib, json, pathlib, time
root = pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience')
here = pathlib.Path(__file__).resolve().parent
manifest = root / 'research/rmaf/algorithm/universal233/ordinary_dispatch/fast_ordinary_recursion/FINAL-MANIFEST-v1.json'
data = json.loads(manifest.read_bytes())
prefix = data['canonical_build'] + '/'
start = time.monotonic()
rows = []
for entry in data['immutable_files']:
    p = entry['path']
    if p.startswith(prefix) and (p.endswith('.olean') or p.endswith('/Ordinary.lean') or p.endswith('/lean-toolchain')):
        actual = hashlib.sha256((root/p).read_bytes()).hexdigest()
        rows.append(dict(path=p, expected=entry['sha256'], actual=actual, match=actual == entry['sha256']))
out = dict(manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),
           count=len(rows), elapsed_seconds=time.monotonic()-start, all_match=all(r['match'] for r in rows), rows=rows)
(here/'PINNED-OBJECTS-v1.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k != 'rows'}))
