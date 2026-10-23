"""Actual separate-producer definition controls; completed audit reuse declared."""
from pathlib import Path
import importlib.util, json, os, subprocess, hashlib
from compatibility import inspect

R = Path(__file__).resolve().parents[6]
D = Path(__file__).resolve().parent
B = D/'build'
old = R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py'
spec = importlib.util.spec_from_file_location('completed_author_audit', old)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
rows = {}
for name in ['LeftValue', 'RightValue', 'TwinValue']:
    out = B/('records-'+name)
    out.mkdir(exist_ok=True)
    source = audit.audit_source([name], [name], out)
    p = B/(name+'Dump.lean')
    p.write_text(source)
    result = subprocess.run([str(R/'bootloops-lean'), str(p)], cwd=B,
        env=dict(os.environ, LEAN_PATH=str(B)), capture_output=True,
        text=True, timeout=30)
    (D/(name+'Dump.log')).write_text(result.stdout+result.stderr)
    assert result.returncode == 0, result.stdout+result.stderr
    actual = json.loads((out/(name+'.json')).read_text())
    rows[name] = [r for r in actual if r['actual_name']=='ProducerPlant.value']
    assert len(rows[name]) == 1 and rows[name][0]['kind']=='definition'

checks = []
for label, names, reject in [
    ('actual-clean-values', ['LeftValue','TwinValue'], False),
    ('actual-different-values-LR', ['LeftValue','RightValue'], True),
    ('actual-different-values-RL', ['RightValue','LeftValue'], True)]:
    result = inspect([r for n in names for r in rows[n]])
    assert bool(result['rejects']) == reject, (label, result)
    checks.append({'control':label, 'expected_reject':reject, 'result':result})
rec = {'completed_author_contact':{'path':str(old.relative_to(R)),
       'sha256':hashlib.sha256(old.read_bytes()).hexdigest()},
       'checks':checks, 'actual_rows':rows,
       'scope':'author instrument controls, not independent scientific verification'}
(D/'COMPATIBILITY-CONTROLS-v1.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({'actual_controls':len(checks),'all_expected':True}))
