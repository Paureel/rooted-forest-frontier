#!/usr/bin/env python3
"""One-shot local packaging and replay. No acceptance inferred from exit alone."""
from pathlib import Path
import subprocess,json,time,hashlib,datetime,re
ROOT=Path(__file__).resolve().parents[5]
HERE=Path(__file__).resolve().parent
RESULT=ROOT/'research/rmaf/results'

def atomic(path,data):
    tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(data,indent=2)+'\n');tmp.replace(path)
def run(args,name,expect):
    start=time.perf_counter()
    r=subprocess.run(args,cwd=ROOT,text=True,capture_output=True,timeout=60)
    path=RESULT/f'thesis-runtime-repair-recurrence-{name}.log'
    path.write_text(r.stdout+r.stderr)
    assert r.returncode==expect,(args,r.returncode,r.stdout,r.stderr)
    return {'command':args,'exit_code':r.returncode,'expected_exit_code':expect,'elapsed_seconds':time.perf_counter()-start,'log':str(path)}
runs=[]
for file,extra,name in [('check_recurrence.py',['--tag','final'],'final'),('check_multiplicative.py',[],'multiplicative'),('check_state_coverage.py',[],'state-coverage')]:
    runs.append(run(['./bootloops-python',str(HERE/file)]+extra,name,0))
runs.append(run(['./bootloops-lean',str(HERE/'RepairArithmetic.lean')],'lean-final',0))
runs.append(run(['./bootloops-lean',str(HERE/'NegativeControl.lean')],'lean-negative',1))
proof=(HERE/'RepairArithmetic.lean').read_text()
# Comments may describe banned constructs; remove comments before token scan.
code=re.sub(r'/\-.*?\-/','',proof,flags=re.S)
code=re.sub(r'--[^\n]*','',code)
assert not re.search(r'\b(sorry|axiom|native_decide|admit)\b',code)
assert 'sorryAx' not in (RESULT/'thesis-runtime-repair-recurrence-lean-final.log').read_text()
base=json.loads((RESULT/'thesis-runtime-repair-recurrence-final.json').read_text())
mult=json.loads((RESULT/'thesis-runtime-repair-recurrence-multiplicative.json').read_text())
coverage=json.loads((RESULT/'thesis-runtime-repair-recurrence-state-coverage.json').read_text())
inputs=[ROOT/'research/rmaf/thesis_complexity/REPAIR-TARGET.md',HERE.parent/'controls-frozen.json',ROOT/'research/rmaf/sources/baseline/whidden-thesis-2013.pdf',ROOT/'research/rmaf/sources/baseline/whidden-thesis-2013.txt',RESULT/'thesis-complexity-reachable-trace.json',RESULT/'thesis-complexity-three-credit-trace.json']
hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
atomic(HERE/'input-ledger.json',{'use':'All are development inputs, not held-out independent certification. No forbidden-route imports.','sha256':hashes})
claims=[
 {'id':'conditional-joint','label':'Conditional joint G4.1 composition','status':'conditional','detail':'Lean proves target from explicit A/B bounds and a finite C-prefix frontier test; source-wide existence of the required certificates remains open.'},
 {'id':'three-credit','label':'Three-credit states included','status':'finite-check','detail':'Ten states 0<=q<=p<=3 are represented. The frozen p=3,q=2 trace has only its cost-two B branch legal. No universal p<=3 cap is imported.'},
 {'id':'state-coverage','label':'Algorithm transition coverage','status':'open','detail':'The proposed finite coefficient table is not asserted to cover arbitrary state transitions or every source history. Explicit closure mutations fail.'},
 {'id':'universal-runtime','label':'Universal runtime repair','status':'open','detail':'No universal G4 bound or O(2^k) acceptance. No source-reachable counterexample to the candidate two-active-leaf lemma is claimed.'}]
lemmas=[
 {'id':'weak-C-interface','label':'Weaker sufficient C allowance','status':'checked','detail':'Kernel-checked: C<=alpha*2^(K-3)+2 suffices given the source A/B allowances; exact when those allowances are attained.'},
 {'id':'affine-frontier','label':'Finite prefix composition','status':'checked','detail':'Kernel-checked list frontier composition, invocation offsets, and use-site composition. Forest-to-prefix interpretation is a separate structural premise.'},
 {'id':'multiplicative-credit','label':'Finite credit arithmetic','status':'checked','detail':'Kernel-checked finite weights, 35 enumerated passing schemas, two retained exceptional schemas, and negative budget -4 with alpha=128.'},
 {'id':'source-frontier-existence','label':'Source-reachable C prefix existence','status':'open','detail':'Requires legal source cuts, priority/orientation, trivial merges/root removals, and valid empty-credit induction exits for every relevant G4 history.'}]
metrics={'named_controls_passed':len(base['controls']),'negative_budget_states':40,'credit_states':10,'enumerated_schemas':len(mult['rows']),'passing_schemas':mult['metrics']['passing_rows'],'exceptional_schemas':len(mult['failures']),'closure_mutations_caught':coverage['metrics']['arithmetic_obstructions'],'positive_lean_exit':runs[-2]['exit_code'],'negative_lean_exit':runs[-1]['exit_code']}
summary={'schema_version':1,'created_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'OPEN-STRUCTURAL-CONDITIONAL-ARITHMETIC','summary':'Conditional G4.1 joint composition checked; required C allowance weakened to alpha*2^(K-3)+2. Universal source coverage remains open.','metrics':metrics,'claims':claims,'lemmas':lemmas,'runs':runs,'independence':{'same_author_python_and_lean':True,'shared_source':str(inputs[2]),'fresh_nonauthor_verification':'not performed by this arm; parent stage required','other_routes_read':False},'structural_hypotheses':['Valid source state, exact oriented pair and first applicable rule','Exact legal branch prefix with every invocation counted once','No extra invocation for trivial merges or root removal','Empty-credit smaller-budget induction at each frontier, or explicit terminal bound','A continuation allowance established separately','C frontier allowance meets explicit aggregate test'],'skipped':['Full algorithm reachability enumeration','Universal forest/protection structural proof','Fresh independent verification and fresh referee simulation','Full BootLoops package suite (no toolkit packages changed)'],'artifacts':[str(HERE/'report.md'),str(HERE/'state-invariant.md'),str(HERE/'RepairArithmetic.lean'),str(HERE/'source-ledger.md'),str(HERE/'review-precheck.md')],'aggregate_theorem_count_changed':False}
atomic(RESULT/'thesis-runtime-repair-recurrence-summary.json',summary)
atomic(HERE/'result.json',summary)
progress={'id':'thesis-runtime-repair-recurrence','title':'Whidden G4 recurrence repair','status':'open','summary':summary['summary'],'metrics':metrics,'claims':claims,'lemmas':lemmas,'artifacts':summary['artifacts']+[str(RESULT/'thesis-runtime-repair-recurrence-summary.json')]}
atomic(ROOT/'research/rmaf/progress/thesis-runtime-repair-recurrence.json',progress)
print(json.dumps({'status':summary['status'],'metrics':metrics,'report':str(HERE/'report.md'),'summary':str(RESULT/'thesis-runtime-repair-recurrence-summary.json')},sort_keys=True))
