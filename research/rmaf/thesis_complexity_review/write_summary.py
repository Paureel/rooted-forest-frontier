"""One-shot report packaging; derives displayed counts from retained receipts."""
import hashlib,json
from pathlib import Path
BASE=Path(__file__).resolve().parents[1];OUT=BASE/'results';HERE=Path(__file__).resolve().parent
control=json.loads((OUT/'thesis-complexity-review-controls.json').read_text())
audit=json.loads((OUT/'thesis-complexity-review-receipt-audit.json').read_text())
replay=json.loads((OUT/'thesis-complexity-review-replay.json').read_text())
assert control['controls_passed']==14 and audit['kernel_axiom_audit_count']==28
summary={
 'id':'thesis-complexity-review','title':'Fresh adversarial review of thesis runtime proof','status':'open',
 'review_complete':True,
 'summary':'Independent graph replay confirms both local source-proof defects; the O(2^q n) theorem remains open. A proposed two-active-leaf repair is recorded separately.',
 'metrics':{'pre_witness_controls_passed':control['controls_passed'],'independent_witnesses':2,'supplied_trace_states_compared':len(audit['trace_comparisons']),
            'diagnostic_arithmetic_rows':audit['diagnostic_count'],'lean_axiom_audits':audit['kernel_axiom_audit_count'],
            'false_proposition_rejected':True,'positive_twin_accepted':True,'asymptotic_lower_bound_proved':False},
 'claims':[
   {'id':'g4-exception','label':'Reachable G4 exceptional substitution','status':'checked','detail':'Source p123 exceptional credit assignments yield 9/16 > 1/2 and affine31 > 30; independent explicit-graph replay reaches the state in the full permitted-call tree. The C-child has no legal further call.'},
   {'id':'credit-cap','label':'Reachable three-credit assignment','status':'checked','detail':'Independent 13-leaf trace reaches P={a,x,u}, Q={x,u}, outside p117 stated |P|≤2. Enlarging the domain may repair this omission.'},
   {'id':'lean-replay','label':'28 stated axiom audits replayed','status':'checked','detail':'Clean source copies import only Std; permitted standard axioms only. Actual false-proposition diagnostic and axiom-free true twins retained.'},
   {'id':'two-leaf-repair','label':'Proposed local repair with two active leaves','status':'open','detail':'A geometric argument plus conditional Lean arithmetic covers the two-active-leaf G4 subcase. Newly authored proof awaits separate review; three/four active leaves remain open.'},
   {'id':'theorem-6-13','label':'Universal runtime theorem','status':'open','detail':'No full recursion bound, asymptotic lower bound, short-circuit reachability theorem, linear local-work implementation proof or root-convention transfer established.'}],
 'lemmas':[],
 'artifacts':['research/rmaf/thesis_complexity_review/report.md','research/rmaf/thesis_complexity_review/source-freeze.md',
              'research/rmaf/thesis_complexity_review/local-repair.md','research/rmaf/thesis_complexity_review/referee_sim_report.md',
              'research/rmaf/thesis_complexity_review/replay.py','research/rmaf/results/thesis-complexity-review-replay.json',
              'research/rmaf/results/thesis-complexity-review-controls.json','research/rmaf/results/thesis-complexity-review-receipt-audit.json',
              'research/rmaf/results/thesis-complexity-review-repair-controls.json',
              'research/rmaf/results/thesis-complexity-review-credit-lean.log','research/rmaf/results/thesis-complexity-review-trace-lean.log',
              'research/rmaf/results/thesis-complexity-review-negative-lean.log','research/rmaf/results/thesis-complexity-review-positive-lean.log',
              'research/rmaf/results/thesis-complexity-review-repair-lean.log'],
 'limits':['Independent source reconstruction, not blind discovery: assignment disclosed headline values.',
           'Source PDF and candidate inputs shared; producer Python runtime neither read nor imported.',
           'Producer Lean replay is kernel reproduction, not an independent universal formalization.',
           'No thesis_correctness or transfer records read. No upstream toolkit changes; general validation suite not run by this review.'],
 'sources':[{'path':'research/rmaf/sources/baseline/whidden-thesis-2013.pdf','locator':'printed pp107,110–111,117–123; root convention p12'}]
}
(OUT/'thesis-complexity-review-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(BASE/'progress/thesis-complexity-review.json').write_text(json.dumps(summary,indent=2)+'\n')
bugs=[{'id':'G4.1-exception','source_step':'printed p123 exceptional A3BC assignments',
       'instance':'nine-leaf graph replay state2','lhs_child_mass':'9/16','rhs_parent_mass':'1/2','residual':'1/16',
       'affine_instance':{'X':4,'child_allowance':31,'parent_allowance':30,'residual':1},
       'claim_scope':'failure of supplied local bound substitution, not actual descendant count or asymptotic theorem'},
      {'id':'G4-credit-domain','source_step':'printed p123 union of incoming P,Q versus p117 state domain',
       'instance':'thirteen-leaf graph replay state4','P':['a','x','u'],'Q':['x','u'],'lhs_cardinality':3,'rhs_cap':2,'residual':1,
       'claim_scope':'literal recursively assigned state outside stated induction domain; no larger-base conclusion'}]
(OUT/'thesis-complexity-review-bugs.json').write_text(json.dumps(bugs,indent=2)+'\n')
hashes={str(p.relative_to(BASE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(HERE.rglob('*')) if p.is_file() and '__pycache__' not in str(p)}
(OUT/'thesis-complexity-review-file-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
print(json.dumps({'summary':'research/rmaf/results/thesis-complexity-review-summary.json','review_complete':True,'runtime_status':'open','bug_reports':len(bugs)}))
