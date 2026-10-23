#!/usr/bin/env python3
"""One-shot source-bound Lean audit for universal233 geometry.

Rebuilds actual graph proofs and the original RMAF dependency, prints every
source theorem's complete axiom list, and requires rejection of both false
controls. It certifies kernel elaboration only; independent proof/interface
review is a separate gate. Uses project wrappers and retains full logs.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
SOURCES = [HERE / n for n in ('Geometry.lean', 'Bridge.lean', 'Composition.lean', 'Controls.lean')]
UPSTREAM = ROOT / 'research/rmaf/lean/RMAF.lean'
ENV = dict(os.environ, LEAN_PATH=str(HERE))

def run(source, log, output=None):
    cmd = [str(ROOT / 'bootloops-lean')]
    if output:
        cmd += ['-o', str(output)]
    cmd += [str(source)]
    start = time.monotonic()
    result = subprocess.run(cmd, cwd=ROOT, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (HERE / log).write_text(result.stdout)
    return {'source': str(source.relative_to(ROOT)), 'log': log,
            'exit': result.returncode, 'seconds': round(time.monotonic() - start, 6)}


def names(source):
    namespace = []
    out = []
    for line in source.read_text().splitlines():
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            namespace.append(m.group(1))
        m = re.match(r'^end(?:\s+(\S+))?\s*$', line)
        if m and namespace:
            namespace.pop()
        m = re.match(r'^theorem\s+([A-Za-z0-9_]+)', line)
        if m:
            out.append('.'.join(namespace + [m.group(1)]))
    return out


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

record = {'classification': 'AUTHOR-DEVELOPMENT; CLOSED-UNVERIFIED pending fresh nonauthor review',
          'scope': 'actual unsuppressed original-address graph geometry and conditional source-core composition',
          'builds': [], 'sources_sha256': {}, 'accepted': False}
for source in [SOURCES[0], UPSTREAM, *SOURCES[1:]]:
    item = run(source, source.stem.lower() + '-audit-build.log', HERE / (source.stem + '.olean'))
    record['builds'].append(item)
    if item['exit']:
        (HERE / 'certificate.json').write_text(json.dumps(record, indent=2) + '\n')
        raise SystemExit('positive build failed: ' + str(source))
all_names = [name for p in [UPSTREAM, *SOURCES] for name in names(p)]
audit = HERE / 'Axioms.lean'
audit.write_text('import Controls\n' + '\n'.join('#print axioms ' + n for n in all_names) + '\n')
item = run(audit, 'axioms.log')
record['axiom_audit'] = item
record['theorem_count'] = len(all_names)
if item['exit']:
    raise SystemExit('axiom audit elaboration failed')
allowed = {'propext', 'Quot.sound', 'Classical.choice'}
reported = {}
for line in (HERE / 'axioms.log').read_text().splitlines():
    m = re.match(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", line)
    if m:
        axioms = {x.strip() for x in (m.group(2) or '').split(',') if x.strip()}
        reported[m.group(1)] = sorted(axioms)
        if not axioms <= allowed:
            raise SystemExit('unapproved axioms: ' + line)
if set(reported) != set(all_names):
    raise SystemExit('incomplete axiom audit')
record['axioms'] = reported
negative = run(HERE / 'FalseControl.lean', 'negative-control.log')
record['negative_control'] = negative
negative_text = (HERE / 'negative-control.log').read_text()
if negative['exit'] == 0 or negative_text.count('is false') != 2:
    raise SystemExit('false proposition controls were not both rejected')
for source in [UPSTREAM, *SOURCES, HERE / 'FalseControl.lean']:
    text = source.read_text()
    # All these modules have ordinary theorem declarations. Ban kernel escapes
    # in executable source; comments are excluded to avoid counting audit prose.
    text = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b', text):
        raise SystemExit('forbidden declaration or tactic in ' + str(source))
for source in [UPSTREAM, *SOURCES, HERE / 'FalseControl.lean', audit, Path(__file__), ROOT / 'bootloops-lean']:
    record['sources_sha256'][str(source.relative_to(ROOT))] = digest(source)
record['accepted'] = True
record['meaning'] = 'all listed theorem proofs kernel-checked with only standard axioms; both false controls rejected; source-core construction, runtime and full solver remain outside this certificate'
(HERE / 'certificate.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS: source-bound positive builds, full axiom audit of', len(all_names), 'theorems, two rejected false controls')
print('Grade: CLOSED-UNVERIFIED; no independent reviewer or source-core coverage certified')
