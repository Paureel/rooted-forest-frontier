from pathlib import Path
import json,hashlib,os
R=Path('/Users/paurel/Documents/ChatGPT/bootscience');P=R/'research/rmaf/algorithm/verification/runtime233-2026-10-15/sol-independent/postrelease-v4';old=P.parent/'postrelease-v3'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
release=R/'research/rmaf/algorithm/verification/runtime233-2026-10-15/ROOT-RELEASE-v4.json';assert sha(release)=='fc8a8794053d00d5d1ca7c14053579103ccbf35155a9a819c59e6138e8be6eaf'
x=json.loads(release.read_text());idx={v['path']:v['sha256'] for v in x['licensed_immutable_files']};assert len(idx)==22667
(P/'LICENSE-INDEX-v4.json').write_text(json.dumps(idx,sort_keys=True,indent=2)+'\n')
roots={
 'invocation':'results/algorithm-universal233-global-resume-20261016T083330Z-20261016T083708893142Z',
 'classifier':'results/algorithm-universal233-rule5-resume-20261016T083330Z-freeze-20261016T085305929640Z',
 'persistent':'results/algorithm-universal233-binary-resume-20261016T083330Z-final-20261016T085734Z',
 'optimizer':'results/algorithm-universal233-optimizer-local-20261016T085144Z-20261016T085502958188Z'}
extra=['results/algorithm-universal233-budget-optimization-replay-20261015T213529360638Z','results/algorithm-universal233-early-resume-20261016T083330Z-20261016T083634190186Z','results/algorithm-universal233-forest-check-root-20261015T211023Z']
# Check collisions using license metadata. Separate exact roots, not arbitrary path union.
seen={};overlaps=[]
for root in [roots['optimizer']]+extra:
 for path,pin in idx.items():
  tail=path.removeprefix(root+'/')
  if path.startswith(root+'/') and '/' not in tail and path.endswith('.olean'):
   if tail in seen:overlaps.append({'basename':tail,'prior':seen[tail],'current':path,'same_olean':idx[seen[tail]]==pin})
   seen[tail]=path
assert not overlaps,overlaps
(P/'IMPORT-BINDING-v4.json').write_text(json.dumps({'roots':roots,'optimizer_additional_roots':extra,'optimizer_direct_basename_collisions':overlaps,'scope':'Four separate canonical lineages; optimizer requires explicit three disjoint exact prior roots. All available direct binary pins are recorded by reused calibrated runner; not a claim of actual transitive import closure. OWBudgets not imported: it imports author OWControls.','global_pool':False},indent=2)+'\n')
mods=[]
def mod(pkg,m,names):
 r=roots[pkg];path=r+'/'+m+'.lean';assert sha(R/path)==idx[path]
 mods.append({'package':pkg+'-'+m,'module':m,'source':path,'source_sha256':idx[path],'canonical_import_root':r,'additional_import_roots':extra if pkg=='optimizer' else [],'theorems':names})
W='OrdinaryDispatch.WorkRecursion.';C='Universal233.Rule5PendantLocalWork.';B='GenericForest.BinaryProvider.';O='OrdinaryDispatch.OptimizerLocalWork.'
mod('invocation','OrdinaryStepTrace',[W+'ordinaryStepTrace_value',W+'ordinaryStepTrace_common'])
mod('invocation','OrdinaryCallBound',[W+'ordinaryCallNodes_eq',W+'ordinaryCallNodes_bound',W+'ordinaryStepTrace_common_or_paid',W+'queryWork_mass_bound'])
mod('classifier','ClassifierPayload',[C+'admitted_value',C+'admitted_work',C+'final_value',C+'final_work',C+'final_calls',C+'final_call_count',C+'final_payload',C+'final_scaled_work'])
mod('persistent','PersistentCapacity',[B+'prepareCapacity_spec',B+'prepareCapacity_width_bound',B+'prepareCapacity_work_bound',B+'partitionFromInput_value',B+'partitionFromInput_work'])
mod('persistent','PersistentEntry',[B+'checkerCapacity_ready',B+'checkerFromInput_projects',B+'checkerFromInput_polynomial'])
mod('optimizer','OWOptimize',[O+'meterScan_accounting',O+'meterPreflight_bound',O+'meterInputCheck_bound',O+'recovery_counter_bound',O+'meterOptimize_value',O+'actual_wrapper_fees',O+'wrapper_polynomial',O+'conditional_233_derived_wrapper'])
plan={'version':'4','scope':'Six exact selected source/interface rechecks; no all-imported-body audit, no author auditor/control execution, no new blind/replication credit. OWBudgets body reviewed only.','initial_subprocess_seconds':60,'disk_floor_bytes':3*1024**3,'lean_MiB':3072,'raw_cap_bytes':16*1024**2,'line_cap_bytes':16*1024**2,'compressed_budget_bytes':256*1024**2,'modules':mods,'new_blind_credit':0}
(P/'RECHECK-PLAN-v4.json').write_text(json.dumps(plan,indent=2)+'\n')
s=(old/'recheck_consumers_v3_1.py').read_text().replace('RECHECK-PLAN-v3.1.json','RECHECK-PLAN-v4.json').replace('LICENSE-INDEX-v3.json','LICENSE-INDEX-v4.json').replace('KERNEL-CONTACT-v3.jsonl','KERNEL-CONTACT-v4.jsonl').replace('six-consumer proof source only','selected v4 consumer proof source only')
(P/'recheck_consumers_v4.py').write_text(s)
controls={
 'BaselineTrue.lean':'example : 2+3=5 := by decide +kernel\n',
 'BaselineFalse.lean':'example : 2+3=6 := by decide +kernel\n',
 'InvocationTruth.lean':'''import OrdinaryCallBound
open RMAF ForestState Universal233
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
example : (ordinaryStepTrace FastOrdinary.solve 0 (.leaf 0) (.leaf 1)).queries.length=0 := by decide +kernel
example : ordinaryCallNodes 0 (.leaf 0) (.leaf 1)=1 := by decide +kernel
example : ordinaryCallNodes 0 (.leaf 0) (.leaf 0)=1 := by decide +kernel
example : queryWork (fun _ _ _=>3) [((.leaf 0,.leaf 1),0),((.leaf 0,.leaf 1),0)]=6 := by decide +kernel
example : callNodeFactor=1024 := by decide +kernel
''',
 'InvocationFalse.lean':'''import OrdinaryCallBound
open RMAF ForestState Universal233
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
example : queryWork (fun _ _ _=>3) [((.leaf 0,.leaf 1),0),((.leaf 0,.leaf 1),0)]=3 := by decide +kernel
''',
 'ClassifierTruth.lean':'''import ClassifierPayload
open RMAF Universal233.Rule5PendantLocalWork
private def r : CheckRequest := .restriction (.leaf 0) (.leaf 0) [0]
private def no : Unit→CheckReceipt Bool := fun _=>⟨false,5,[r]⟩
private def yes : Unit→CheckReceipt Bool := fun _=>⟨true,7,[r,r]⟩
private def optionRow (n : Nat) : CheckReceipt (Option Nat) := ⟨if n=0 then some 9 else none,2,[r]⟩
example : (andSequence [no,yes]).value=false := by decide +kernel
example : (andSequence [no,yes]).work=6 := by decide +kernel
example : (andSequence [no,yes]).calls.length=1 := by decide +kernel
example : (andSequence [fun _=>⟨true,5,[r]⟩,yes]).work=18 := by decide +kernel
example : (optionsMeter optionRow [0,1,0]).value=[9,9] := by decide +kernel
example : (optionsMeter optionRow [0,1,0]).work=19 := by decide +kernel
example : (optionsHeadMeter ⟨[0,1,0],10⟩ optionRow).work=31 := by decide +kernel
example : (admittedMeter (fun _=>0) (.leaf 0) (.leaf 1) 0 1).value=false := by decide +kernel
example : (admittedMeter (fun _=>0) (.leaf 0) (.leaf 1) 0 1).work>1 := by decide +kernel
''',
 'ClassifierFalse.lean':'''import ClassifierPayload
open RMAF Universal233.Rule5PendantLocalWork
private def r : CheckRequest := .restriction (.leaf 0) (.leaf 0) [0]
example : (andSequence [fun _=>⟨false,5,[r]⟩,fun _=>⟨true,7,[r,r]⟩]).work=18 := by decide +kernel
''',
 'PersistentTruth.lean':'''import PersistentEntry
open GenericForest.BinaryProvider
example : (zeroRegister [(),()]).work=9 := by decide +kernel
example : (widenCapacity [] [false,false,false]).value.length=3 := by decide +kernel
example : (widenCapacity [] [false,false,false]).work=13 := by decide +kernel
example : (spineCounter [10,20,30]).value=[true,true] := by decide +kernel
example : (countLabel [(),()] [true] [[true],[true,false],[]]).value=[false,true] := by decide +kernel
example : (partitionFromInput [[true]] [[[true,false]]]).value=true := by decide +kernel
example : (partitionFromInput [[true]] [[[true],[true,false]]]).value=false := by decide +kernel
example : (checkerFromInput none [] [] []).value.isSome=true := by decide +kernel
example : (checkerFromInput (some (.leaf [true])) [.leaf [true,false]] [] [[[true]]]).value.isSome=true := by decide +kernel
example : (checkerFromInput (some (.node (.leaf [true]) (.leaf [true,false]))) [.node (.leaf [true]) (.leaf [true,false])] [] [[[true]]]).value.isNone=true := by decide +kernel
''',
 'PersistentFalse.lean':'''import PersistentEntry
open GenericForest.BinaryProvider
example : (containsLabel [true] [[true,false]]).value=false := by decide +kernel
''',
 'OptimizerTruth.lean':'''import OWOptimize
open RMAF Universal233.WholeSourceWork OrdinaryDispatch.OptimizerLocalWork
private def query (q : Nat) : Charged (Option (List (List Nat))) := ⟨if q=1 then some [[7]] else none,5⟩
example : (meterScan query 0 4).value.trials.length=2 := by decide +kernel
example : (meterScan query 0 4).value.selected=some (1,[[7]]) := by decide +kernel
example : (meterScan query 0 4).work=34 := by decide +kernel
example : (meterScan query 0 4).administration=24 := by decide +kernel
example : (meterScan (fun _=>⟨none,5⟩) 0 2).work=36 := by decide +kernel
example : (meterScan query 0 0).work=2 := by decide +kernel
example : (meterLength [10,20,30]).work=14 := by decide +kernel
example : (meterFinish (.leaf 0) ⟨none,[]⟩).work=8 := by decide +kernel
example : preflightFee 1=1024 := by decide +kernel
''',
 'OptimizerFalse.lean':'''import OWOptimize
open RMAF Universal233.WholeSourceWork OrdinaryDispatch.OptimizerLocalWork
private def query (q : Nat) : Charged (Option (List (List Nat))) := ⟨if q=1 then some [[7]] else none,5⟩
example : (meterScan query 0 4).work=17 := by decide +kernel
'''}
(P/'own-controls').mkdir()
for name,body in controls.items():(P/'own-controls'/name).write_text(body)
spec='''# Own hand-truth controls, frozen before execution

Same contacted reviewer: postcontact, zero blind or replication credit. Baseline2+3=5 and false6 reuse calibrated engine. Source formulas were read first; these are controls for evaluation/accounting, not independent theorem-production or native timing evidence.

Invocation: malformed source pair has no queries and one invocation; identical single leaf has one invocation. Two literal query occurrences of cost3 sum to6; corruption deduplicates to3.

Classifier: false guard of work5 short-circuits to6 and one request. All-true work5/7 guards with1/2 requests and terminal1 give second7+1+2+1=11 then5+11+1+1=18. options evaluates all three work2/one-request rows even failure/duplicate; each adds2+1+3=6, with terminal1 yields19 and [9,9]. Input materialization10 and head2 give31. Malformed admitted refuses but still pays strict partition. Corruption charges later guard after false.

Persistent: capacity2 zero register costs4*2+1=9. Three raw false bits widen to capacity3 at4*3+1=13 (no trimming by numerical value). Binary3 is[true,true]; padded1=[true,false] equals1, so count over1,padded1,0 is2=[false,true]. A singleton padded1 partition agrees; repeated1 fails. Empty represented state succeeds; one-leaf padded source equals target and succeeds; repeated target labels refuse. Corruption treats padded1 as unequal.

Optimizer: callback work5; success at budget1 after failed0 yields two trials and work(5+12)+(5+12)=34, administration24. Two failed calls add terminal2 giving36. Zero fuel costs2. Three-item length4*3+2=14; no selected recovery finish8; preflightFee1=256*4=1024. Corruption omits first failed callback and claims17.

All negatives contain one false assertion expected to be diagnosed as false by decide +kernel. No author control source is imported. OWBudgets is excluded because it imports OWControls. These finite controls are not an exhaustive actual-tree census or a native primitive correspondence.
'''
(P/'OWN-CONTROL-SPEC-v4.md').write_text(spec)
items=[]
for name in controls:
 pkg=next((k.lower() for k in ['Invocation','Classifier','Persistent','Optimizer'] if name.startswith(k)),None)
 file='own-controls/'+name
 items.append({'name':name[:-5],'source':file,'source_sha256':sha(P/file),'root':roots[pkg] if pkg else '', 'additional_import_roots':extra if pkg=='optimizer' else [],'expected':'false' if 'False' in name else 'pass','statements':controls[name].count('example :')})
cp={k:v for k,v in plan.items() if k not in ['modules','scope']};cp.update({'fixture':'OWN-CONTROL-SPEC-v4.md','fixture_sha256':sha(P/'OWN-CONTROL-SPEC-v4.md'),'items':items})
(P/'OWN-CONTROL-PLAN-v4.json').write_text(json.dumps(cp,indent=2)+'\n')
s=(old/'run_own_controls_v3_1.py').read_text().replace('v3 controls adapter','v4 controls adapter').replace('OWN-CONTROL-PLAN-v3.1.json','OWN-CONTROL-PLAN-v4.json').replace('BASELINE-CONTROL-RECEIPT-v3.1.json','BASELINE-CONTROL-RECEIPT-v4.json')
(P/'run_own_controls_v4.py').write_text(s)
for f in ['LICENSE-INDEX-v4.json','IMPORT-BINDING-v4.json','RECHECK-PLAN-v4.json','recheck_consumers_v4.py','OWN-CONTROL-SPEC-v4.md','OWN-CONTROL-PLAN-v4.json','run_own_controls_v4.py']:
 (P/f).chmod(0o444)
for p in (P/'own-controls').iterdir():p.chmod(0o444)
print('Frozen',len(mods),'module plans;',sum(i['statements'] for i in items if i['expected']=='pass'),'truth statements including baseline;',sum(i['statements'] for i in items if i['expected']=='false'),'false statements including baseline; disjoint optimizer roots checked.')
