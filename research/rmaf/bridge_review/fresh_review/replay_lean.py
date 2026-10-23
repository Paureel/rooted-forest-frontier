#!/usr/bin/env python3
"""One-shot fresh source replay; writes only in fresh_review/lean_replay.

Compiles unchanged source with a freshly rebuilt dependency and checks printed
axioms. Expected-false files must fail on a false proposition, not import errors.
This is another run of the same Lean kernel, not an independent proof kernel.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

BASE = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
OUT = HERE / 'lean_replay'
OUT.mkdir(exist_ok=True)
CERT = BASE / 'research/rmaf/bridge_review/lean/audit/certificate.json'
cert = json.loads(CERT.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


before = {name: digest(BASE / name) for name in cert['source_hashes']}
assert before == cert['source_hashes'], 'Certificate source hash mismatch'
env = dict(os.environ)
env['LEAN_PATH'] = str(OUT)
rows = []
for module, source, good in [
    ('PureBridge', 'research/rmaf/pure_bridge/lean/PureBridge.lean', True),
    ('GraphRegion', 'research/rmaf/bridge_review/lean/GraphRegion.lean', True),
    ('GraphControls', 'research/rmaf/bridge_review/lean/GraphControls.lean', True),
    ('CleanEdge', 'research/rmaf/bridge_review/lean/positive/CleanEdge.lean', True),
    ('FalseDisconnected', 'research/rmaf/bridge_review/lean/negative/FalseDisconnected.lean', False),
    ('FalseNoMinimum', 'research/rmaf/bridge_review/lean/negative/FalseNoMinimum.lean', False),
    ('FalseSuppressParent', 'research/rmaf/bridge_review/lean/negative/FalseSuppressParent.lean', False),
]:
    command = [str(BASE / 'bootloops-lean'), '-o', str(OUT / (module + '.olean')), str(BASE / source)]
    start = time.perf_counter()
    run = subprocess.run(command, cwd=BASE, env=env, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, timeout=30)
    elapsed = time.perf_counter() - start
    (OUT / (module + '.log')).write_text(run.stdout)
    if good:
        assert run.returncode == 0, (module, run.stdout)
        assert 'sorryAx' not in run.stdout and 'error:' not in run.stdout, (module, run.stdout)
    else:
        assert run.returncode != 0, ('False theorem was accepted', module)
        assert re.search(r'proposition[\s\S]*is false', run.stdout), (module, 'Wrong failure', run.stdout)
        assert 'unknown module' not in run.stdout, (module, run.stdout)
    rows.append({'module': module, 'command': command, 'seconds': elapsed,
                 'exit_code': run.returncode, 'expected_success': good,
                 'log': str((OUT / (module + '.log')).relative_to(BASE))})

axioms = {}
for module in ['PureBridge', 'GraphRegion', 'GraphControls']:
    log = (OUT / (module + '.log')).read_text()
    for name, deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S):
        axioms[name] = [s.strip() for s in deps.split(',') if s.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        axioms[name] = []
assert axioms == cert['axioms'], ('Axiom inventory differs', axioms)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(v) <= allowed for v in axioms.values())
after = {name: digest(BASE / name) for name in before}
assert after == before, 'Source changed during replay'
review_theorem_count = sum(len(re.findall(r'^theorem\b', (BASE / path).read_text(), re.M))
                          for path in ['research/rmaf/bridge_review/lean/GraphRegion.lean',
                                       'research/rmaf/bridge_review/lean/GraphControls.lean'])
assert review_theorem_count == 18
receipt = {'status': 'PASS_FRESH_SOURCE_REPLAY', 'source_hashes': before,
           'source_hashes_unchanged': True, 'certificate_hashes_match': True,
           'axiom_inventory_matches': True, 'allowed_axioms': sorted(allowed),
           'review_theorem_count': review_theorem_count, 'executions': rows,
           'axioms': axioms, 'script_sha256': digest(Path(__file__)),
           'scope': 'Same Lean kernel and original consumer; fresh clean dependency/output replay only.'}
(HERE / 'lean_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({k: v for k, v in receipt.items() if k not in ['axioms', 'source_hashes']}, indent=2))
