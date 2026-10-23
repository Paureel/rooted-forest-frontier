"""One-shot source-preserving Lean rebuild and negative-control audit."""
from pathlib import Path
import subprocess, os, json, hashlib, re, time
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');R=ROOT/'research/rmaf/thesis_correctness/repair';OUT=R/'review/lean-build';OUT.mkdir(exist_ok=True)
env=dict(os.environ);env['LEAN_PATH']=str(OUT)
files=[R/'edge_route/OriginalEdges.lean',R/'edge_route/RootedPaths.lean',R/'component_route/EmptyRoot.lean',R/'TwoExchangeCost.lean',ROOT/'research/rmaf/thesis_correctness_review/lean-isolated/ExistentialRepair.lean',R/'ExistentialConsumers.lean',R/'edge_route/PositiveControls.lean',R/'edge_route/RootedPathControls.lean']
negative=[R/'edge_route/NegativeControl.lean',R/'component_route/EmptyRootNegative.lean']
rows=[]
for src in files+negative:
    before=hashlib.sha256(src.read_bytes()).hexdigest();t=time.perf_counter();cmd=[str(ROOT/'bootloops-lean'),'-o',str(OUT/(src.stem+'.olean')),str(src)]
    run=subprocess.run(cmd,cwd=ROOT,env=env,capture_output=True,text=True,timeout=60)
    log=run.stdout+run.stderr;(OUT/(src.stem+'.log')).write_text(log)
    after=hashlib.sha256(src.read_bytes()).hexdigest();assert before==after
    axioms={}
    for name,contents in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log):axioms[name]=[s.strip() for s in contents.split(',') if s.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms",log):axioms[name]=[]
    ok=run.returncode!=0 if src in negative else run.returncode==0
    if src not in negative:
        ok=ok and all(set(v)<={'propext','Quot.sound','Classical.choice'} for v in axioms.values())
        ok=ok and not re.search(r'\b(sorry|admit|axiom|native_decide)\b',re.sub(r'/\-.*?\-/|--[^\n]*','',src.read_text(),flags=re.S))
    row={'source':str(src),'sha256':before,'returncode':run.returncode,'negative_control':src in negative,'accepted':ok,'axioms':axioms,'elapsed_seconds':time.perf_counter()-t,'log':str(OUT/(src.stem+'.log'))}
    rows.append(row);print(json.dumps({k:row[k] for k in ['source','returncode','negative_control','accepted','elapsed_seconds']}),flush=True)
    if not ok:break
receipt={'status':'passed' if len(rows)==len(files+negative) and all(x['accepted'] for x in rows) else 'failed','rows':rows,'source_hashes_unchanged':True,'positive_denominator':len(files),'negative_denominator':len(negative),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'research/rmaf/results/thesis-correctness-repair-review-lean.json').write_text(json.dumps(receipt,indent=2)+'\n');assert receipt['status']=='passed'
