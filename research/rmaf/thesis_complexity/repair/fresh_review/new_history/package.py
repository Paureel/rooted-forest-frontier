"""Package the separate history addendum; preserve first-review results."""
from pathlib import Path
import json,hashlib
base=Path(__file__).resolve().parent;rmaf=base.parents[3];workspace=base.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
replay=json.loads((rmaf/'results/thesis-runtime-repair-fresh-review-history-replay.json').read_text())
lean=json.loads((rmaf/'results/thesis-runtime-repair-fresh-review-history-lean.json').read_text())
assert all(x['passed'] for x in replay['checks'])
assert lean['positive_exit_code']==0 and lean['all_13_standard_axioms_only'] and lean['false_outside_copy_rejected']
assert sha(workspace/lean['source'])==lean['source_sha256']
first_path=rmaf/'results/thesis-runtime-repair-fresh-review-final.json';first=json.loads(first_path.read_text())
progress_path=rmaf/'progress/thesis-runtime-repair-fresh-review.json';progress=json.loads(progress_path.read_text())
saved=base/'progress-before-history.json'
if not saved.exists():saved.write_text(json.dumps(progress,indent=2)+'\n')
old=json.loads(saved.read_text())
receipt={'id':'thesis-runtime-repair-fresh-review-history','status':'checked','summary':'Independent reachable counterexample to the unqualified history-to-outside-b application premise; conditional geometric theorem and runtime bound not refuted.','first_review':{'status':first['status'],'receipt':str(first_path.relative_to(workspace)),'sha256':sha(first_path),'preserved_unchanged':True},'metrics':{'exact_replay_checks':len(replay['checks']),'source_branch_steps':4,'ordinary_labels':12,'J_budget':16,'J_pendants':3,'J_e_active_roots':3,'actual_C_count':replay['actual_C']['count'],'original_Lean_statements':11,'supplemental_Lean_checks':2,'false_Lean_copy_rejected':1},'fire':replay['fire'],'source_correspondence':{'G1_C_assignment':'p118 sets P={a},Q empty for A2 C; all-three-legal is not required','G3_sole_child':'p120 resets P,Q on sole A2/A3 child; physical protections persist','G3_endpoint':'p120 old A2/current A2 two-child endpoint retains a,Q empty','depth':'p110 physical protected top restricts eligibility independently of P/Q'},'formal_limits':lean['limits'],'actual_C':replay['actual_C'],'artifacts':[str((base/'ADDENDUM.md').relative_to(workspace)),str((rmaf/'results/thesis-runtime-repair-fresh-review-history-replay.json').relative_to(workspace)),str((rmaf/'results/thesis-runtime-repair-fresh-review-history-lean.json').relative_to(workspace))],'input_sha256':replay['input_sha256'],'implementation_lineage':'Fresh evaluator authored during first review, copied with only root/output relocation; no parent witness generator or engine imported.'}
(rmaf/'results/thesis-runtime-repair-fresh-review-history-final.json').write_text(json.dumps(receipt,indent=2)+'\n')
progress=old.copy();progress['status']='conditional';progress['summary']='First conditional review preserved. New independent history refutes its proposed unqualified outside-b application lemma; source runtime repair remains open.'
progress['first_review']={'status':old['status'],'summary':old['summary'],'receipt':str(first_path.relative_to(workspace)),'sha256':sha(first_path)}
progress['metrics']=dict(old['metrics'],history_replay_checks=60,history_application_fires=1,history_actual_C_count=2,history_Lean_checks=13)
progress['claims']=old['claims']+[{'id':'history-outside-b-application','label':'Unqualified reachable history implies outside-b','status':'checked','detail':'False: independent 12-leaf C,A,C,A history reaches qualifying J with x inside protected b; membership residual 1. Conditional theorem and runtime inequality not refuted.'}]
progress['lemmas']=[dict(l,status='checked',detail='The proposed conjunction including outside-b placement is false by the new reachable witness. Retained-a/protected-sibling subclaims themselves are not refuted.') if l['id']=='active-a-history' else l for l in old['lemmas']]
progress['artifacts']=old['artifacts']+receipt['artifacts']+[str((rmaf/'results/thesis-runtime-repair-fresh-review-history-final.json').relative_to(workspace))]
progress_path.write_text(json.dumps(progress,indent=2)+'\n')
p=base/'ADDENDUM.md';s=p.read_text().replace('Status: running. The first review and its receipts remain unchanged.','Status: checked reachable application-premise failure. The first review and its receipts remain unchanged.');p.write_text(s)
print(json.dumps({'status':receipt['status'],'first_review_status':first['status'],'metrics':receipt['metrics']}))
