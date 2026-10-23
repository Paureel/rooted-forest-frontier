"""One-shot isolated build and standard-axiom audit for this proof route."""
from pathlib import Path
import os,re,json,subprocess,time,hashlib
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');HERE=ROOT/'research/rmaf/thesis_correctness/repair/edge_route';RESULT=ROOT/'research/rmaf/results'
out=HERE/'lean-audit';out.mkdir(exist_ok=True)
inputs=['OriginalEdges.lean','RootedPaths.lean','PositiveControls.lean','RootedPathControls.lean','NegativeControl.lean']
hashes={n:hashlib.sha256((HERE/n).read_bytes()).hexdigest() for n in inputs}
for n in inputs:
 s=(HERE/n).read_text()
 assert not re.search(r'\b(sorry|axiom|native_decide)\b',s),n
records=[];env=dict(os.environ,LEAN_PATH=str(out));start=time.perf_counter()
for n in inputs:
 cmd=[str(ROOT/'bootloops-lean')]
 if n in ['OriginalEdges.lean','RootedPaths.lean']:cmd+=['-o',str(out/(Path(n).stem+'.olean'))]
 cmd+=[str(HERE/n)]
 began=time.perf_counter();r=subprocess.run(cmd,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=RESULT/('thesis-correctness-repair-edge-audit-'+Path(n).stem+'.log');log.write_text(r.stdout)
 expected_failure=n=='NegativeControl.lean'
 if expected_failure:assert r.returncode!=0 and 'proved that the proposition' in r.stdout and 'is false' in r.stdout
 else:assert r.returncode==0 and 'sorryAx' not in r.stdout and 'error:' not in r.stdout and 'warning:' not in r.stdout,(n,r.stdout)
 deps=[]
 for x in re.findall(r'depends on axioms: \[([^\]]*)\]',r.stdout,re.S):
  names=[y.strip() for y in x.split(',') if y.strip()];assert set(names)<={'propext','Classical.choice','Quot.sound'};deps.extend(names)
 records.append({'file':str(HERE/n),'command':cmd,'returncode':r.returncode,'expected_failure':expected_failure,'log':str(log),'elapsed_seconds':time.perf_counter()-began,'axiom_union':sorted(set(deps))})
assert hashes=={n:hashlib.sha256((HERE/n).read_bytes()).hexdigest() for n in inputs}
result={'status':'SCOPED-FORMAL-CHECKS-PASS','universal_AF_normalization':'OPEN','named_theorems':26,'controls_positive_named':2,'negative_control_rejected':True,'fresh_import_directory':str(out),'source_hashes':hashes,'commands':records,'elapsed_seconds':time.perf_counter()-start,'scope':'Original-edge list algebra, ranked parent paths, graph walks and conditional corridor isolation. No AF preservation theorem.'}
p=RESULT/'thesis-correctness-repair-edge-formal-audit.json';tmp=p.with_suffix('.tmp');tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(p)
print(json.dumps({'status':result['status'],'named_theorems':26,'negative_control_rejected':True,'elapsed_seconds':result['elapsed_seconds']}))
