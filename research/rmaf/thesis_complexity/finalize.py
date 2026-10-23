#!/usr/bin/env python3
"""One-shot record assembly from this arm's retained receipts; no theorem validator."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[1];H=Path(__file__).resolve().parent
arith=json.loads((R/'results/thesis-complexity-arithmetic.json').read_text())
t1=json.loads((R/'results/thesis-complexity-reachable-trace.json').read_text())
t2=json.loads((R/'results/thesis-complexity-three-credit-trace.json').read_text())
logs={f:(R/'results'/f).read_text() for f in ['thesis-complexity-lean.log','thesis-complexity-trace-lean.log','thesis-complexity-lean-negative.log']}
for f in ['thesis-complexity-lean.log','thesis-complexity-trace-lean.log']:
 assert 'error' not in logs[f] and 'sorryAx' not in logs[f],f
for f in ['Credit.lean','Trace.lean']:
 s=(H/f).read_text(); assert not re.search(r'\bsorry\b|\bnative_decide\b|^\s*axiom\s',s,re.M)
assert 'is false' in logs['thesis-complexity-lean-negative.log']
arts=['research/rmaf/thesis_complexity/report.md','research/rmaf/thesis_complexity/transition-ledger.md','research/rmaf/thesis_complexity/source-notes.md','research/rmaf/thesis_complexity/Credit.lean','research/rmaf/thesis_complexity/Trace.lean','research/rmaf/results/thesis-complexity-arithmetic.json','research/rmaf/results/thesis-complexity-reachable-trace.json','research/rmaf/results/thesis-complexity-three-credit-trace.json','research/rmaf/results/thesis-complexity-lean.log','research/rmaf/results/thesis-complexity-trace-lean.log','research/rmaf/results/thesis-complexity-lean-negative.log']
claims=[
 {'id':'g4-exception-arithmetic','label':'Exceptional G4 bound substitution','status':'checked','detail':'Exact 9/16 > 1/2 coefficient; affine gap X-3 universally proved in Lean. Checks concern the supplied bound substitution, not actual runtime.'},
 {'id':'g4-reachable','label':'Nine-leaf exceptional transition','status':'tested','detail':'Depth rule, ordered predicates, protection and cuts checked by same-author Python and Lean predicates; fresh source-model review pending.'},
 {'id':'three-credits','label':'Reachable cardinality-three analysis state','status':'tested','detail':'13-leaf trace reaches P={a,x,u},Q={x,u} under literal G4 union instruction; formal finite predicates compiled.'},
 {'id':'theorem-6-13','label':'Universal O(2^q n) theorem','status':'open','detail':'A joint G4 estimate or strengthened C-child bound, expanded state domain, per-node linear overhead proof, and fresh semantic review remain.'},
 {'id':'smallest-obligation','label':'G4.1 empty-Q three-pendant joint bound','status':'open','detail':'For every reachable J with P={a},Q=empty,s=3, derive 1+I_A+I_B+I_C <= B(K,1,0). Sufficient candidate: I_C <= alpha*2^(K-3)-1; unproved for G4 subtrees with three/four active leaves.'}
]
metrics={'arithmetic_control_cases':len(arith['control_results']),'structural_control_cases':t1['controls']['count'],'diagnostic_transition_rows':len(arith['transitions']),'witness_leaf_counts_excluding_rho':[t1['leaf_count_excluding_rho'],t2['leaf_count_excluding_rho']],'lean_axiom_prints':sum(v.count('axioms:')+v.count('does not depend on any axioms') for k,v in logs.items() if k!='thesis-complexity-lean-negative.log'),'lean_negative_control_rejected':True}
out={'id':'thesis-complexity','title':'Whidden Chapter 6 independent complexity reconstruction','status':'open','summary':'Reachable local credit-substitution gap and three-credit state documented; universal runtime theorem remains open.','metrics':metrics,'claims':claims,'artifacts':arts,'limits':['No asymptotic lower-bound counterexample.','No full MAF solver or universal algorithm semantics formalized.','Python and Lean are same-author translations; fresh source-to-model review required.','No unaugmented-root transfer or novelty claim.','Toolkit suite not run by this arm; no upstream toolkit changes.'],'source_sha256':'0dd9ced63f26ab608dc484cfe853d52171565b0cc704bb61336dd64a15c2bbe9'}
(R/'results/thesis-complexity-summary.json').write_text(json.dumps(out,indent=2)+'\n')
(R/'progress/thesis-complexity.json').write_text(json.dumps({k:out[k] for k in ['id','title','status','summary','metrics','claims','artifacts']},indent=2)+'\n')
manifest={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [H/'controls-frozen.json',H/'trace-controls-frozen.json',H/'Credit.lean',H/'Trace.lean',H/'FalseCredit.lean',H/'recurrence_audit.py',H/'reachable_trace.py',H/'three_credit_trace.py']}
(H/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status':out['status'],'metrics':metrics,'accepted_lean_logs_without_errors':True}))
