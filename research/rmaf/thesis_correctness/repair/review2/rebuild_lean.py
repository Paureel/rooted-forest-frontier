#!/usr/bin/env python3
"""One-shot clean rebuild of unchanged local formal constituents, not AF proofs."""
from pathlib import Path
import subprocess,json,hashlib,os,re,time
B=Path(__file__).resolve().parent
W=B.parents[4]
R=B.parent
L=B/'lean-build';L.mkdir(exist_ok=True)
lean=W/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
assert lean.exists(),(W,lean)
sources=[
('OriginalEdges',R/'edge_route/OriginalEdges.lean'),
('RootedPaths',R/'edge_route/RootedPaths.lean'),
('EmptyRoot',R/'component_route/EmptyRoot.lean'),
('TwoExchangeCost',R/'TwoExchangeCost.lean'),
('ExistentialRepair',W/'research/rmaf/thesis_correctness_review/lean-isolated/ExistentialRepair.lean'),
('ExistentialConsumers',R/'ExistentialConsumers.lean'),
('PositiveControls',R/'edge_route/PositiveControls.lean'),
('RootedPathControls',R/'edge_route/RootedPathControls.lean'),
('NegativeControl',R/'edge_route/NegativeControl.lean'),
('EmptyRootNegative',R/'component_route/EmptyRootNegative.lean')]
env=dict(os.environ);env['LEAN_PATH']=str(L)
version=subprocess.check_output([str(lean),'--version'],text=True)
rows=[]
for name,source in sources:
    data=source.read_bytes();target=L/(name+'.lean');target.write_bytes(data)
    clean=re.sub(r'/\-.*?\-/','',data.decode(),flags=re.S)
    clean=re.sub(r'--[^\n]*','',clean)
    forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide)\b',clean)
    assert not forbidden,(name,forbidden)
    t0=time.perf_counter()
    p=subprocess.run([str(lean),'-o',str(L/(name+'.olean')),str(target)],cwd=L,env=env,text=True,capture_output=True,timeout=60)
    log=p.stdout+p.stderr;(L/(name+'.log')).write_text(log)
    negative='Negative' in name
    assert (p.returncode!=0)==negative,(name,p.returncode,log)
    if not negative:
      assert 'sorryAx' not in log
      for deps in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log):
        assert set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',deps)) <= {'propext','Classical.choice','Quot.sound'},(name,deps)
    rows.append({'module':name,'source':str(source),'sha256':hashlib.sha256(data).hexdigest(),'unchanged_copy':data==target.read_bytes(),'returncode':p.returncode,'expected_rejection':negative,'elapsed_seconds':time.perf_counter()-t0,'printed_axiom_checks':len(re.findall(r"'[^']+' (?:depends on axioms|does not depend on any axioms)",log)),'log':str(L/(name+'.log'))})
# The original control source omits a print for parent_rank; audit it explicitly.
audit=L/'AxiomAudit.lean';audit.write_text('import RootedPathControls\n#print axioms parent_rank\n')
p=subprocess.run([str(lean),str(audit)],cwd=L,env=env,text=True,capture_output=True,timeout=60)
(L/'AxiomAudit.log').write_text(p.stdout+p.stderr)
assert p.returncode==0 and 'sorryAx' not in p.stdout
for name,source in sources: assert hashlib.sha256(source.read_bytes()).hexdigest()==next(r['sha256'] for r in rows if r['module']==name)
d={'version':version.strip(),'entries':rows,'positive_modules':sum(not r['expected_rejection'] for r in rows),'negative_controls_rejected':sum(r['expected_rejection'] for r in rows),'extra_parent_rank_audit':p.stdout.strip(),'scope':'Unchanged local definitions, walks, binary-cut bounds, arithmetic and conditional logic only; no kernel AF normalization or global correctness theorem.'}
(B/'lean.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2))
