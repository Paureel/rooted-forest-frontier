#!/usr/bin/env python3
"""One-shot evidence packager; checks saved bounded run, Lean and negative control."""
import hashlib,json,subprocess
from pathlib import Path
ROOT=Path.cwd();D=ROOT/'research/rmaf/thesis_complexity/repair/geometry';R=ROOT/'research/rmaf/results'
def atom(path,v):
    temp=path.with_suffix(path.suffix+'.tmp');temp.write_text(json.dumps(v,indent=2)+'\n');temp.replace(path)
def lean(name,out):
    q=subprocess.run(['./bootloops-lean',str(D/name)],capture_output=True,text=True)
    (R/out).write_text(q.stdout+q.stderr)
    return q.returncode
positive=lean('Geometry.lean','thesis-runtime-repair-geometry-lean-final.log')
negative=lean('FalseGeometry.lean','thesis-runtime-repair-geometry-lean-negative-final.log')
assert positive==0 and negative!=0
run=json.loads((R/'thesis-runtime-repair-geometry-search20000-v5.json').read_text())
assert run['script_sha256']==hashlib.sha256((D/'check-v5.py').read_bytes()).hexdigest()
forest=json.loads((R/'thesis-runtime-repair-geometry-forest20000.json').read_text())
assert forest['script_sha256']==hashlib.sha256((D/'check.py').read_bytes()).hexdigest()
assert forest['hits']=={'3':194,'4':152} and forest['geometries']==20000
assert forest['maxima']=={'3':'1/4','4':'1/4'}
disconnected=json.loads((R/'thesis-runtime-repair-geometry-disconnected.json').read_text())
assert disconnected['status']=='PASS' and disconnected['legal_end_branches']==0
assert run['geometries']==20000 and run['hits']=={'3':539,'4':336}
assert all(x=='1/4' for x in run['maxima'].values())
assert len(run['controls'])==6
# Passing twin and a deliberate strengthening which the exact maximum refutes.
from fractions import Fraction
assert all(Fraction(x)<=Fraction(1,4) for x in run['maxima'].values())
assert any(Fraction(x)>Fraction(1,8) for x in run['maxima'].values())
claims=[
 {'id':'GEO-universal','label':'Universal joint runtime theorem','status':'open','detail':'Not certified. Candidate source-history argument and changed frontier annotation need fresh nonauthor verification; A/B allowances are external hypotheses.'},
 {'id':'GEO-local','label':'Conditional three/four-root C allowance','status':'proposed-unverified','detail':'PROOF.md derives C <= alpha*2^(K-3)-1 from stated history, rules, and empty-credit frontier induction, explicitly handling a,x,u protection. Source geometry is not fully formalized.'},
 {'id':'GEO-bounded','label':'Bounded exact geometry check','status':'executed-no-fire','detail':'40000 seeded generated geometries in connected/forest runs, 1221 qualifying states (733 three-root, 488 four-root), maximum exit mass 1/4 in both classes. Generated states are not claimed top-level reachable.'},
 {'id':'GEO-controls','label':'Frozen control replay','status':'executed-pass','detail':'Nine-leaf 9/16 and dead C, thirteen-leaf three credits, live two-root, wrong orientation and positive twin reproduced; protected sibling erasure mutation caught.'}
]
lemmas=[
 {'id':'GEO-survival','label':'No sibling cuts preserve a descendant','status':'lean-checked-conditional','detail':'surviving_descendant on explicit CutTree; source-cut-family-to-premise implication remains ordinary proof.'},
 {'id':'GEO-arithmetic','label':'Conditional local and joint arithmetic','status':'lean-checked','detail':'Geometry.lean: 13 theorems total, including negative fact and finite small-budget allowances; no custom axioms, sorry, or native_decide.'},
 {'id':'GEO-source-geometry','label':'No free merger and protected pair distance','status':'ordinary-argument-pending-review','detail':'312 bounded no-free-merger checks, 104 connected two-protected distance checks, plus an explicit disconnected dead control; source proof in Lemma5 needs independent review.'}
]
combined={key:run['metrics'].get(key,0)+forest['metrics'].get(key,0) for key in set(run['metrics'])|set(forest['metrics'])}
combined['max_active_protections']=max(run['metrics']['max_active_protections'],forest['metrics']['max_active_protections'])
metrics={**combined,'geometries_checked':40000,'qualifying_three_root':733,'qualifying_four_root':488,'controls_passed':7,'lean_theorems':13,'positive_lean_exit':positive,'negative_lean_exit':negative,'max_discounted_exit_mass':'1/4','connected_search_seconds':run['elapsed_seconds'],'forest_search_seconds':forest['elapsed_seconds']}

receipt={'schema_version':1,'status':'conditional-candidate-unverified','metrics':metrics,'claims':claims,'lemmas':lemmas,'forbidden_cross_reading':'No adversary/parent/recurrence/correctness/transfer implementations read. Allowed source and frozen witnesses shared. Own checker is discovery evidence, not independent certification of own proof.','files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.glob('*')) if p.is_file()},'pending':['Fresh nonauthor source-tree proof review','Source-to-frontier annotation amendment review','Composition with independently established A and B child bounds']}
atom(R/'thesis-runtime-repair-geometry-final.json',receipt)
atom(ROOT/'research/rmaf/progress/thesis-runtime-repair-geometry.json',receipt)
print(json.dumps({'status':receipt['status'],'metrics':metrics}))
