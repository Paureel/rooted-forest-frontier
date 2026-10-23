#!/usr/bin/env python3
"""Kernel-checked fixed prerelease counterexamples to dropping target disjointness."""
import importlib.util,json,sys
from pathlib import Path
H=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('own_readout',H/'actual_readouts_v2.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m);a=m.a
a.OUT=a.RMAF/'results/algorithm-rank-restriction-fresh-clearing-counterproofs-v1.json';a.state={'runs':[],'audits':{},'all_main_milestones':'OPEN','scope':'Refutes only the stronger unguarded reverse extension, not the released guarded theorem'}
p=json.loads((H/'frozen-ready-v1/results/algorithm-rank-restriction-fresh-actual-clearing-v1.json').read_text());cs=m.clear['cases'];lines=['import Requests\nopen RMAF Universal233 Universal233.CoreProgram Universal233.Assembly VertexGeometry\nnamespace FreshClearingCounterexamples\n']
for i,(f,row) in enumerate(zip(cs,p['cases'])):
 assert f['id']==row['id'];o=row['bad_output'];S=m.tree(f['S']);T=m.tree(f['T']);ps=m.parts(o['partition']);cuts='['+','.join('['+','.join('false' if c=='0' else 'true' for c in v)+']' for v in o['cuts'])+']';vs=['['+','.join('false' if c=='0' else 'true' for c in v)+']' for v in f['requested_vertices']];req='(.at '+vs[0]+')' if len(vs)==1 else '(.both '+vs[0]+' '+vs[1]+')'
 name='one' if i==0 else 'two';lines += [f'def S_{name} : Tree := {S}',f'def T_{name} : Tree := {T}',f'def o_{name} : Output := ⟨{ps},{cuts}⟩']
 lines.append(f'''theorem actual_{name}_clearing_target_overlap :
    o_{name} ∈ (generate S_{name} (localColor T_{name} {req}) {f['budget']}).outputs ∧
    partitionCheck (leaves S_{name}) o_{name}.partition = true ∧
    partitionCheck (leaves T_{name}) o_{name}.partition = true ∧
    pairwiseEmbeddings S_{name} o_{name}.partition = true ∧
    pairwiseEmbeddings T_{name} o_{name}.partition = false ∧
    o_{name}.partition.all (fun b => { '['+','.join(vs)+']' }.all
      (fun v => !(minimalVertices b T_{name}).contains v)) = true ∧
    o_{name}.partition.all (fun U =>
      match restrict U T_{name},restrict U S_{name} with
      | some t,some s => agreement t s [U]
      | _,_ => false) = true ∧
    agreement T_{name} S_{name} o_{name}.partition = false := by decide
#print axioms actual_{name}_clearing_target_overlap
''')
lines.append('end FreshClearingCounterexamples');folder=a.BUILD/'rank';(folder/'FreshClearingCounterexamples.lean').write_text('\n'.join(lines)+'\n')
try:
 a.compile_one(folder,'FreshClearingCounterexamples');x=a.audit(folder,'FreshCounterproofOriginAudit',['FreshClearingCounterexamples'],['FreshClearingCounterexamples']);assert not x['bad']
 a.state['verdict']='PASS-TWO-KERNEL-CHECKED-ACTUAL-OUTPUT-CLEARING-COUNTEREXAMPLES';a.save();print(a.state['verdict'])
except Exception as e:a.state['verdict']='OPEN-COUNTERPROOF-FAILURE';a.state['error']=repr(e);a.save();raise
