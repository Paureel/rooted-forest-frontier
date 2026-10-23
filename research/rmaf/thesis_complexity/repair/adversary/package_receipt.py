"""One-shot receipt packaging; does not accept a scientific theorem."""
import hashlib,json,subprocess
from pathlib import Path
from datetime import datetime,timezone
root=Path.cwd();here=root/'research/rmaf/thesis_complexity/repair/adversary';results=root/'research/rmaf/results'
lean=[]
for name,expect,tag in [('AdversaryArithmetic.lean',0,'pass'),('FalseArithmeticControl.lean',1,'planted-failure')]:
    run=subprocess.run([str(root/'bootloops-lean'),str(here/name)],capture_output=True,text=True)
    output=run.stdout+run.stderr
    log=results/f'thesis-runtime-repair-adversary-lean-final-{tag}.log';log.write_text(output)
    assert run.returncode==expect,(name,run.returncode,output)
    if expect:assert 'error' in output
    lean.append({'source':str(here/name),'exit_code':run.returncode,'expected_exit_code':expect,'log':str(log)})
search=json.loads((results/'thesis-runtime-repair-adversary-search20000.json').read_text())['search']
controls=json.loads((results/'thesis-runtime-repair-adversary-controls-v3.json').read_text())
assert controls['control']['mutation_catches']==2 and len(controls['control']['controls'])==5
assert search['fires']==[]
files=['README.md','SPEC.md','PROOF-ATTEMPT.md','finite_check.py','history_cut_control.py','AdversaryArithmetic.lean','FalseArithmeticControl.lean']
receipt={'schema_version':1,'date':datetime.now(timezone.utc).isoformat(),'grade':'NO-FIRE / OPEN structural formalization','controls':{'frozen_fixtures':5,'fresh_evaluator_passed':5,'production_mutation_catches':2,'scope':'exposed calibration controls; not held-out theorem certification'},'search':search,'lean':lean,'structural_claims_formalized':False,'source_history_refuted':False,'out_of_regime_strengthening_refuted':True,'aggregate_theorem_count_changed':False,'files':{str(here/f):hashlib.sha256((here/f).read_bytes()).hexdigest() for f in files},'excluded_inputs_read':False}
path=results/'thesis-runtime-repair-adversary-final.json';path.write_text(json.dumps(receipt,indent=2)+'\n')
progress={'id':'thesis-runtime-repair-adversary','title':'Runtime repair: independent adversary','status':'complete','summary':'No in-regime fire for two-active-leaf repair. Source-history proof must use prescribed cut shapes; tree formalization and global runtime theorem remain open.','updated_at':receipt['date'],'metrics':{'frozen_controls_passed':5,'mutation_catches':2,'sampled_local_trees':search['attempts'],'admissible_J_orientations':search['eligible'],'C_orientations':search['live']+search['dead'],'live_C':search['live'],'dead_C':search['dead'],'singleton_history_checks':search['history_checks'],'in_regime_fires':0,'elapsed_search_seconds':search['seconds']},'claims':[{'id':'two-active-adversary','label':'Two-active-leaf geometric repair','status':'screened','detail':'Finite fresh implementation found no counterexample. Independent ordinary proof attempt retained; not a formal tree theorem.'},{'id':'history-strengthening','label':'Arbitrary simultaneous-cut history strengthening','status':'refuted','detail':'Protected b=(x,y) can be erased by simultaneous cuts of x,y. This is outside source branch rules and does not refute source history.'}],'lemmas':[{'id':'repair-affine-arithmetic','label':'Conditional scaled affine implication','status':'checked','detail':'Lean kernel checked positive-denominator coefficient arithmetic, scaled integer affine implication, height inequalities, and budget drop. A deliberately false arithmetic control failed.'},{'id':'protected-history-structure','label':'Source cut-shape preservation','status':'open','detail':'Ordinary exhaustive-case attempt for singleton, pendant-path, and BCY sets; no formal structural theorem and no held-out author verification.'}],'artifacts':[str(path),str(here/'PROOF-ATTEMPT.md'),str(here/'AdversaryArithmetic.lean'),str(results/'thesis-runtime-repair-adversary-search20000.json'),str(results/'thesis-runtime-repair-adversary-controls-v3.json'),str(results/'thesis-runtime-repair-adversary-history-premise.json')],'sources':[str(root/'research/rmaf/sources/baseline/whidden-thesis-2013.pdf')]}
progress_path=root/'research/rmaf/progress/thesis-runtime-repair-adversary.json';temp=progress_path.with_suffix('.tmp');temp.write_text(json.dumps(progress,indent=2)+'\n');temp.replace(progress_path)
print(json.dumps({'receipt':str(path),'progress':str(progress_path),'grade':receipt['grade'],'controls':5,'mutation_catches':2,'lean_expected_outcomes':len(lean),'fires':0}))
