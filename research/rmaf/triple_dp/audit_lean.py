"""Problem-specific Lean build and destructive-control receipt generator."""
import hashlib
import json
import os
import pathlib
import re
import subprocess
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[2]
env = dict(os.environ)
env['ELAN_HOME'] = str(ROOT / '.runtime/elan')
deps = HERE / '.deps'
deps.mkdir(exist_ok=True)
env['LEAN_PATH'] = ':'.join((str(HERE), str(deps)))
# Rebuild the shared semantics into this route's directory, without changing
# upstream files or relying on an unverified stale compiled dependency.
dep_source = HERE.parent / 'lean/RMAF.lean'
dep_cmd = [str(ROOT/'bootloops-lean'), '-o', str(deps/'RMAF.olean'), str(dep_source)]
dependency = subprocess.run(dep_cmd,env=env,cwd=ROOT,text=True,capture_output=True)
dep_output = dependency.stdout + dependency.stderr
(HERE/'shared-semantics-build.log').write_text(dep_output)
assert dependency.returncode == 0 and 'sorryAx' not in dep_output, dep_output
rows = []
for name in ['TripleDP.lean', 'SemanticControls.lean', 'NegativeControl.lean']:
    src = HERE / name
    start = time.perf_counter()
    cmd = [str(ROOT / 'bootloops-lean'), str(src)]
    if name != 'NegativeControl.lean':
        cmd[1:1] = ['-o', str(src.with_suffix('.olean'))]
    result = subprocess.run(cmd, env=env, cwd=ROOT, text=True, capture_output=True)
    output = result.stdout + result.stderr
    log = HERE / (src.stem + '-audit.log')
    log.write_text(output)
    negative = name == 'NegativeControl.lean'
    if negative:
        assert result.returncode != 0 and 'error:' in output, output
        assert 'decide' in output and 'false' in output, output
    else:
        assert result.returncode == 0, output
        assert 'sorryAx' not in output, output
        assert re.search(r'\b(sorry|admit|native_decide)\b', src.read_text()) is None
        assert re.search(r'^\s*axiom\b', src.read_text(), re.MULTILINE) is None
    axioms = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
    for theorem, names in axioms:
        assert set(filter(None, (x.strip() for x in names.split(',')))) <= {'propext', 'Classical.choice', 'Quot.sound'}
    rows.append(dict(file=name, returncode=result.returncode, negative=negative,
                     checked_axioms=axioms, sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
                     seconds=time.perf_counter()-start, log=str(log.relative_to(ROOT))))
version = subprocess.run([str(ROOT/'bootloops-lean'),'--version'],env=env,cwd=ROOT,text=True,capture_output=True)
assert version.returncode == 0 and '4.35.0' in version.stdout
receipt = dict(status='passed', version=version.stdout.strip(), builds=rows,
               theorem_count=sum(len(r['checked_axioms']) for r in rows if not r['negative']),
               shared_semantics=dict(source=str(dep_source.relative_to(ROOT)),
                                     sha256=hashlib.sha256(dep_source.read_bytes()).hexdigest(),
                                     rebuilt=True, log='research/rmaf/triple_dp/shared-semantics-build.log'),
               limitations=['Full graph/MAF-to-DP correspondence remains OPEN.',
                            'SemanticControls shares RMAF.lean executable definitions.',
                            'Generic table is a specification; Python refinement is not formally linked.'])
path = HERE.parent / 'results/triple-dp-lean.json'
tmp = path.with_suffix('.tmp')
tmp.write_text(json.dumps(receipt,indent=2)+'\n')
tmp.replace(path)
print(json.dumps(dict(status=receipt['status'],theorem_count=receipt['theorem_count'],
                     negative_control='caught')))
