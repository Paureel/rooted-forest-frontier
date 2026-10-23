"""Wrapper replay of the original fresh-author checks; source and scientific checks unchanged."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import re
import subprocess
import time

HERE=Path(__file__).resolve().parent
ROUTE=HERE.parent
RMAF=HERE.parents[1]
WORKSPACE=HERE.parents[3]
RESULTS=RMAF/'results'
REPLAY=HERE/'connected_wrapper_replay'
DEPS=REPLAY/'deps'
OUTPUT=RESULTS/'triple-dp-verification-connected-wrapper.json'
assert not OUTPUT.exists(), 'preserve existing receipt'
DEPS.mkdir(parents=True,exist_ok=True)
LEAN=WORKSPACE/'bootloops-lean'
expected_hashes={
 'TripleDP.lean':'6b544504b68dd6638caa40200914dee5720be1cdc38ce5f180de1dc792944298',
 'ConnectedRegions.lean':'1b09d6e197d26eef62dfa5b13b8f5e17e826867e8778e68b50bc4f7b02d8ea33',
 'NegativeConnected.lean':'9ea7ecb0d1121d68039e31db6634e63da5f7e43e2e11d250f552b74d9a391d12'}
expected_new=['lca_prefix_left','pathConvex_lca_closed','rooted_pathConvex_iff_prefixClosed',
 'pathConvex_child_restriction','rooted_child_contains_root','rooted_region_decomposition',
 'gapped_region_lca_closed','gapped_region_not_pathConvex']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for name,wanted in expected_hashes.items():
    assert sha(ROUTE/name)==wanted, 'changed source: '+name
    source=(ROUTE/name).read_text()
    assert not re.search(r'\b(sorry|admit|unsafe)\b|^\s*axiom\s',source,re.M)
    (REPLAY/name).write_bytes((ROUTE/name).read_bytes())
positive=REPLAY/'PositiveConnected.lean'
positive.write_text('import ConnectedRegions\nopen TripleDP\ntheorem positive_connected_vertex : gappedRegion [false, false] := Or.inr rfl\n#print axioms positive_connected_vertex\n')
# Expectations are fixed before execution: dependency 19, extension 8,
# false-path-vertex rejection at decide, and a passing same-import clean twin.
receipt={'utc':datetime.now(timezone.utc).isoformat(),'source_hashes':expected_hashes,
 'script_sha256':sha(Path(__file__)),'positive_control_sha256':sha(positive),
 'expected_counts':{'dependency':19,'extension':8,'clean_twin':1},'builds':[],
 'scope':'single-region path-convex address decomposition; G2 family/cost correspondence OPEN',
 'full_theorem_verdict':'OPEN'}
env=os.environ.copy(); env['LEAN_PATH']=str(DEPS)
env['ELAN_HOME']=str(WORKSPACE/'.runtime/elan')
original_receipt=RESULTS/'triple-dp-verification-connected.json'
original_record=json.loads(original_receipt.read_text())
preserved={str(original_receipt):sha(original_receipt)}
for row in original_record['builds']:
    path=WORKSPACE/row['log']
    preserved[str(path)]=sha(path)
receipt['launcher']={'path':str(LEAN),'sha256':sha(LEAN),'ELAN_HOME':env['ELAN_HOME'],
    'change':'Execution launcher changed to workspace wrapper; source contents and scientific checks unchanged. Receipt/log/build-output destinations are separate.'}
receipt['prior_receipt_sha256']=sha(original_receipt)
receipt['prior_receipt_and_logs_before']=preserved
assert receipt['source_hashes']==original_record['source_hashes']
assert receipt['positive_control_sha256']==original_record['positive_control_sha256']
version=subprocess.run([str(LEAN),'--version'],cwd=WORKSPACE,env=env,text=True,capture_output=True,timeout=30)
assert version.returncode==0 and '4.35.0' in version.stdout
receipt['lean_version']=version.stdout.strip()
start=time.perf_counter()
def build(name,source,olean=None,negative=False):
    command=[str(LEAN)]
    if olean is not None:command+=['-o',str(olean)]
    command.append(str(source))
    began=time.perf_counter()
    p=subprocess.run(command,cwd=WORKSPACE,env=env,text=True,capture_output=True,timeout=30)
    output=p.stdout+p.stderr
    log=RESULTS/('triple-dp-verification-connected-wrapper-'+name+'.log')
    assert not log.exists()
    log.write_text(output)
    audits=[]
    for theorem,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output):
        names=[a.strip() for a in axioms.split(',') if a.strip()]
        assert set(names)<={'propext','Classical.choice','Quot.sound'},(theorem,names)
        audits.append({'theorem':theorem,'axioms':names})
    for theorem in re.findall(r"'([^']+)' does not depend on any axioms",output):
        audits.append({'theorem':theorem,'axioms':[]})
    row={'name':name,'command':command,'returncode':p.returncode,'seconds':time.perf_counter()-began,
         'negative':negative,'axiom_audits':audits,'log':str(log.relative_to(WORKSPACE)),
         'log_sha256':sha(log)}
    receipt['builds'].append(row)
    if negative:
        assert p.returncode!=0, 'false path vertex compiled'
        assert 'decide' in output and 'false' in output, 'negative failure lacks expected false-proposition diagnostic'
        assert 'object file' not in output and 'unknown module' not in output, 'negative import failure is not a control catch'
    else:assert p.returncode==0,output
    return row
try:
    a=build('dependency',REPLAY/'TripleDP.lean',DEPS/'TripleDP.olean')
    assert len(a['axiom_audits'])==19
    b=build('extension',REPLAY/'ConnectedRegions.lean',DEPS/'ConnectedRegions.olean')
    assert {x['theorem'] for x in b['axiom_audits']}=={'TripleDP.'+x for x in expected_new}
    c=build('negative',REPLAY/'NegativeConnected.lean',negative=True)
    d=build('clean-twin',positive)
    assert len(d['axiom_audits'])==1
    for name,wanted in expected_hashes.items():assert sha(ROUTE/name)==wanted
    for path,wanted in preserved.items():assert sha(Path(path))==wanted
    receipt['prior_receipt_and_logs_preserved']=True
    receipt['replay_verdict']='PASS'
except Exception as exc:
    receipt['replay_verdict']='FAIL';receipt['error']=repr(exc)
    raise
finally:
    receipt['seconds']=time.perf_counter()-start
    OUTPUT.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'replay_verdict':receipt.get('replay_verdict'),'seconds':receipt['seconds'],
                     'output':str(OUTPUT),'new_theorem_audits':len(receipt['builds'][1]['axiom_audits']) if len(receipt['builds'])>1 else 0}))
