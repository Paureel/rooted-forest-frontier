"""One-shot replay of the TreeAddresses semantic proof and frozen controls.
Uses existing bootloops Python/Lean wrappers. The toolkit index has no tree
occurrence formalization package; this is problem-specific evidence plumbing.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
DEPS = HERE / 'replay-deps'
LOGS = HERE / 'replay-logs'
DEPS.mkdir(exist_ok=True)
LOGS.mkdir(exist_ok=True)
source = ROOT / 'research/rmaf/lean/RMAF.lean'
module = HERE / 'TreeAddresses.lean'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
initial = {str(p.relative_to(ROOT)): sha(p) for p in
           [source, module, HERE / 'controls.json', HERE / 'semantic_controls.py', Path(__file__)]}
receipt = {'utc_started': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'source_hashes': initial, 'runs': [], 'status': 'running',
           'provenance': 'Author replay. RMAF source, Lean kernel, and address mathematics shared with construction. Python stack traversal shares no candidate Lean code, but its same-author controls are not a fresh nonauthor certification.'}
def save():
    (HERE / 'replay-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
save()

def run(name, args, expect_success=True, expected_error=None):
    env = os.environ.copy()
    env['LEAN_PATH'] = str(DEPS)
    start = time.monotonic()
    result = subprocess.run(args, cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    (LOGS / (name + '.log')).write_text(result.stdout)
    row = {'id': name, 'label': name, 'returncode': result.returncode,
           'elapsed_seconds': time.monotonic() - start,
           'log': str((LOGS / (name + '.log')).relative_to(ROOT))}
    accepted = result.returncode == 0 if expect_success else result.returncode != 0
    if expected_error is not None:
        accepted = accepted and expected_error in result.stdout
    row['status'] = 'pass' if accepted else 'fail'
    row['detail'] = 'expected success' if expect_success else 'expected rejection'
    receipt['runs'].append(row)
    save()
    assert accepted, name + '\n' + result.stdout
    return result.stdout

try:
    run('semantic-controls', ['./bootloops-python', str(HERE / 'semantic_controls.py')])
    run('fresh-rmaf', ['./bootloops-lean', '-o', str(DEPS / 'RMAF.olean'), str(source)])
    run('tree-addresses', ['./bootloops-lean', '-o', str(DEPS / 'TreeAddresses.olean'), str(module)])
    text = module.read_text()
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', text)
    assert not forbidden, forbidden
    names = re.findall(r'^theorem\s+([\w.]+)', text, re.MULTILINE)
    audit = HERE / 'AxiomAudit.lean'
    audit.write_text('import TreeAddresses\n' + ''.join(
        '#print axioms LeastEmbedding.' + name + '\n' for name in names))
    axioms = run('axioms', ['./bootloops-lean', str(audit)])
    assert len(axioms.splitlines()) == len(names)
    found = re.findall(r'\[([^\]]*)\]', axioms)
    allowed = {'propext', 'Quot.sound', 'Classical.choice'}
    for group in found:
        assert set(group.split(', ')) <= allowed, group
    receipt['axiom_audit'] = {'status': 'pass', 'declarations': names,
                              'allowed': sorted(allowed), 'log_sha256': sha(LOGS / 'axioms.log')}
    controls = json.loads((HERE / 'controls.json').read_text())
    def tree(t):
        return f'(.leaf {t})' if isinstance(t, int) else f'(.node {tree(t[0])} {tree(t[1])})'
    def addr(a):
        return '[' + ', '.join('false' if c == '0' else 'true' for c in a) + ']'
    def addrs(xs):
        return '[' + ', '.join(map(addr, xs)) + ']'
    lines = ['import TreeAddresses', 'open RMAF LeastEmbedding', 'namespace SemanticControls']
    for f in controls['fixtures']:
        t, selection = tree(f['tree']), str(f['selection'])
        lines += [f'theorem {f["id"]}_vertices : vertices {t} = {addrs(f["vertices"])} := by decide',
                  f'theorem {f["id"]}_terminals : terminals {selection} {t} = {addrs(f["terminals"])} := by decide']
        for j, (a, x) in enumerate(f['occurrences']):
            lines += [f'theorem {f["id"]}_occurrence_{j} : LeafOccurrence {t} {addr(a)} {x} := by',
                      '  apply (mem_terminals_iff.mp (show ' + addr(a) + ' ∈ terminals [' + str(x) + '] ' + t + ' by decide)).elim',
                      '  intro y hy',
                      '  have he : y = ' + str(x) + ' := by simpa using hy.2',
                      '  subst y', '  exact hy.1']
    lines += ['theorem repeated_labels_two_addresses :',
              '    LeafOccurrence (.node (.leaf 5) (.leaf 5)) [false] 5 ∧',
              '    LeafOccurrence (.node (.leaf 5) (.leaf 5)) [true] 5 ∧',
              '    ([false] : Vertex) ≠ [true] :=',
              '  ⟨.left (.leaf 5), .right (.leaf 5), by decide⟩',
              'theorem invalid_address_rejected :',
              '    ¬ ValidVertex (.node (.leaf 5) (.leaf 5)) [false, false] := by',
              '  intro h',
              '  have hm := mem_vertices_iff.mpr h',
              '  have hn : [false, false] ∉ vertices (.node (.leaf 5) (.leaf 5)) := by decide',
              '  exact hn hm', 'end SemanticControls']
    (HERE / 'SemanticControls.lean').write_text('\n'.join(lines) + '\n')
    run('kernel-controls', ['./bootloops-lean', str(HERE / 'SemanticControls.lean')])
    negative = [
        ('MissingOccurrence', 'terminals [5] (.node (.leaf 5) (.leaf 5)) = [[false]]'),
        ('InvalidAmbient', '[false, false] ∈ vertices (.node (.leaf 5) (.leaf 5))'),
        ('DuplicateSelection', 'terminals [5, 5] (.leaf 5) = [[], []]')]
    for name, proposition in negative:
        p = HERE / (name + '.lean')
        p.write_text('import TreeAddresses\nopen RMAF LeastEmbedding\nexample : ' + proposition + ' := by decide\n')
        run(name, ['./bootloops-lean', str(p)], False, 'decide')
    malformed = HERE / 'MalformedProof.lean'
    malformed.write_text('import TreeAddresses\nexample : True := by exact (0 : Nat)\n')
    run('MalformedProof', ['./bootloops-lean', str(malformed)], False, 'Type mismatch')
    assert all(sha(ROOT / p) == h for p, h in initial.items()), 'source changed during audit'
    receipt['status'] = 'pass'
    receipt['scope'] = 'Kernel-checked semantic vocabulary only; protocol grade CLOSED-UNVERIFIED pending parent nonauthor review and consumer trace.'
except Exception as exc:
    receipt['status'] = 'fail'
    receipt['error'] = str(exc)
    save()
    raise
save()
print('PASS: fresh RMAF and TreeAddresses builds; standard-only axiom audit.')
print('PASS: frozen fixtures in Python and Lean; 3 false semantic claims and malformed proof rejected.')
print('Scope: address semantics only; fresh nonauthor acceptance remains with parent.')
