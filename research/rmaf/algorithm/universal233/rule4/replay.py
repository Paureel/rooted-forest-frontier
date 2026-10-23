#!/usr/bin/env python3
"""One-shot isolated Rule4 exact-source replay and amended occurrence audit.
Uses only completed frozen development proof contacts. No toolkit-wide suite.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,sys,time,copy
D=Path(__file__).resolve().parent;ROOT=D.parents[4]
sys.path.insert(0,str(D))
from audit_support import audit_source,parse_occurrences
OUT=ROOT/'results'/('algorithm-universal233-rule4-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
OUT.mkdir()
ENV=dict(os.environ,LEAN_PATH=str(OUT))
OWN=['Rule4OriginalExchange','Rule4PathPrune','Rule4Graft','Rule4SourceExchange','Rule4Exchange','Rule4LcaCoverage','Rule4Cover','Rule4LiteralCuts','Rule4LiteralChecks','Rule4Selector','Rule4Costs','Rule4Program','Rule4Solve','Rule4Controls']
record={'runner_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'audit_support_sha256':hashlib.sha256((D/'audit_support.py').read_bytes()).hexdigest(),'status':'RUNNING_AUTHOR_SOURCE_BOUND_RULE4','all_three_main_milestones':'OPEN','independent_acceptance':False,'source_inputs':[],'runs':[],'detector_control_results':{},'timing':{'basis':'Same-host 29-module 16.588s and extra frozen-closure 13.005s measured development builds; own modules individually <1s.','plan':'One isolated full-source build; no tree-pair census; per-command timeout60s; monitor completed module rows.'}}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check_pin(p,expected):
 if digest(p)!=expected:raise AssertionError('SOURCE_PIN_MISMATCH: '+str(p))
def save():(OUT/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
def run(name,build=False):
 start=time.monotonic();p=subprocess.run([str(ROOT/'bootloops-lean')]+(['-o',str(OUT/(name+'.olean'))] if build else [])+[str(OUT/(name+'.lean'))],cwd=ROOT,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (OUT/(name+'.log')).write_text(p.stdout);record['runs'].append({'module':name,'exit':p.returncode,'seconds':round(time.monotonic()-start,6)});save();return p
control_pin=json.loads((D/'AUDIT-CONTROLS-v1.json').read_text())
for rel,h in control_pin['pins'].items():assert digest(ROOT/rel)==h,('DETECTOR_PIN',rel)
assert digest(D/'audit_support.py')==control_pin['instrument']['sha256']
for n in ['DetectorAlpha','DetectorBeta','DetectorHostile']:
 (OUT/(n+'.lean')).write_bytes((D/'detector'/(n+'.lean')).read_bytes())
 p=run(n,True);assert p.returncode==0,p.stdout
checks=[('DetectorClean',['DetectorAlpha','DetectorBeta'],False),('DetectorBadAB',['DetectorAlpha','DetectorHostile'],True),('DetectorBadBA',['DetectorHostile','DetectorAlpha'],True)]
coalesced=[]
for name,mods,bad in checks:
 dest=OUT/(name+'.json');(OUT/(name+'.lean')).write_text(audit_source(mods,mods,dest))
 p=run(name);assert (p.returncode!=0)==bad,p.stdout
 data=json.loads(dest.read_text());rows=parse_occurrences(data,mods,bad)
 record['detector_control_results'][name]={'expected_reject':bad,'actual_exit':p.returncode,'occurrences':len(rows),'direct_axiom_occurrences':sum(r['kind']=='axiom' for r in rows),'same_named_rows':[{k:r[k] for k in ['producer','index','actual_name','resolved_origin','kind']} for r in rows if r['actual_name']=='DetectorShared.shared']}
 if bad:
  coalesced += [r for r in rows if r['producer']=='DetectorHostile' and r['actual_name']=='DetectorShared.shared' and r['resolved_origin']!='DetectorHostile']
 else:
  assert len([r for r in rows if r['actual_name']=='DetectorShared.shared'])==2,'CLEAN_TWINS_NOT_STORED'
  clean=data
assert coalesced,'COALESCED_HOSTILE_NOT_EXERCISED'
for label,mutate in [('missing_occurrence',lambda d:d['occurrences'].pop()),('duplicate_occurrence',lambda d:d['occurrences'].append(copy.deepcopy(d['occurrences'][0])))]:
 corrupt=copy.deepcopy(clean);mutate(corrupt)
 try:parse_occurrences(corrupt,['DetectorAlpha','DetectorBeta'])
 except AssertionError as e: record['detector_control_results'][label]={'caught':True,'reason':str(e)}
 else:raise AssertionError('CORRUPTION_SURVIVED '+label)
# Instrument proved capable before the candidate evidence is opened by it.
record['detector_control_results']['coalesced_hostile_caught']=True
save();print('Amended detector controls passed.',flush=True)

source_ledger=D/'SOURCE-INPUTS-v1.json'
if not source_ledger.exists():source_ledger=D/'dev/source-inputs.json'
sources=json.loads(source_ledger.read_text())
record['source_ledger_sha256']=digest(source_ledger)
for row in sources:
 p=ROOT/row['source'];check_pin(p,row['sha256'])
for n in OWN:sources.append({'module':n,'source':str((D/(n+'.lean')).relative_to(ROOT)),'sha256':digest(D/(n+'.lean'))})
seen=set()
for row in sources:
 n=row['module'];assert n not in seen,('MODULE_COLLISION',n);seen.add(n)
 p=ROOT/row['source'];data=p.read_bytes()
 stripped=re.sub(r'/\-.*?\-/',lambda m:'\n'*m.group().count('\n'),data.decode(),flags=re.S)
 stripped=re.sub(r'--[^\n]*','',stripped)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',stripped),('PROOF_ESCAPE',n)
 (OUT/(n+'.lean')).write_bytes(data)
 record['source_inputs'].append({**row,'compiled_sha256':digest(OUT/(n+'.lean')),'adaptation':'none; exact bytes'})
(OUT/'lean-toolchain').write_bytes((ROOT/'research/rmaf/lean/lean-toolchain').read_bytes())
for i,row in enumerate(sources):
 p=run(row['module'],True)
 assert p.returncode==0 and 'declaration uses' not in p.stdout and 'sorryAx' not in p.stdout,(row['module'],p.stdout)
 if (i+1)%20==0:print('Built',i+1,'/',len(sources),'actual source modules.',flush=True)
(OUT/'Rule4False.lean').write_bytes((D/'Rule4False.lean').read_bytes())
p=run('Rule4False');assert p.returncode!=0 and p.stdout.count('is false')==5,p.stdout
assert '(43300 : Rat)/54289' in (OUT/'Rule4Controls.log').read_text(),'EXACT_MASS_PRINT'
mods=[r['module'] for r in sources]
(OUT/'OccurrenceAudit.lean').write_text(audit_source(['Rule4Controls'],mods,OUT/'occurrences.json'))
p=run('OccurrenceAudit');assert p.returncode==0,p.stdout
actual=json.loads((OUT/'occurrences.json').read_text());rows=parse_occurrences(actual,mods)
for r in rows:
 r['type_sha256']=hashlib.sha256(r['type'].encode()).hexdigest();r['body_sha256']=hashlib.sha256(r['body'].encode()).hexdigest()
(OUT/'occurrences.json').write_text(json.dumps(actual,indent=2)+'\n')
# Recheck every source after actual compilation/audit; no body or import adaptation.
for row in record['source_inputs']:
 check_pin(ROOT/row['source'],row['sha256'])
 check_pin(OUT/(row['module']+'.lean'),row['compiled_sha256'])
plant=OUT/'SourcePinPlant.lean';sample=OUT/'Rule4Cover.lean';plant.write_bytes(sample.read_bytes()+b'\n-- deliberate exact source corruption\n')
try:check_pin(plant,digest(sample))
except AssertionError as e:record['source_pin_plant_rejection']=str(e)
else:raise AssertionError('SOURCE_CORRUPTION_SURVIVED')
(OUT/'Interfaces.lean').write_text('import Rule4Controls\n'+ '\n'.join('#check Universal233.Rule4.'+n for n in ['actual_original_exchange','actual_rule4_cover','selected_cover','select_complete','selected_branches_cover','selected_source_state','all_pendant_literal_regions','selected_swapped_cost','actual_callback_decrease','actual_callback_mass','ExactChild','solveForest_minimum','solveForest_exists','solveForest_none_iff','solveCuts_original','solveCuts_recovery_work'])+'\n')
p=run('Interfaces');assert p.returncode==0,p.stdout
check_pin(Path(__file__),record['runner_sha256'])
check_pin(D/'audit_support.py',record['audit_support_sha256'])
record.update(status='PASS_AUTHOR_RULE4_SOURCE_BOUND_REPLAY',positive_source_modules=len(mods),producer_occurrences=len(rows),resolved_unique_scientific_names=len({r['actual_name'] for r in rows}),producer_counts=actual['producer_counts'],axiom_union=sorted({a for r in rows for a in r['axiom_references']}),false_propositions_rejected=5,source_pin_corruption_caught=True,source_body_adaptations=0,mathematical_scope='Universal original Rule4 no-larger graph cover, actual finite selector/source states, child-IH conditional minimum and final original cuts; exact strict budget decrease and rational callback mass; qualified polynomial source work.',remaining='Fresh nonauthor semantic/interface/source-cost/prose review. Complete universal solver, global recurrence, smaller base and novelty remain OPEN.')
save()
(OUT/'VERDICT.txt').write_text(record['status']+': '+str(len(mods))+' actual exact-source modules; '+str(len(rows))+' stored producer occurrences; standard axioms only; 5 false scientific claims rejected; amended coalesced-axiom/missing/duplicate/source-pin controls caught. Author evidence; fresh nonauthor acceptance and all main milestones OPEN.\n')
if not (D/'RULE4-MANIFEST-v1.json').exists():(D/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
print(record['status'],len(mods),'modules',len(rows),'producer occurrences',flush=True)
print(OUT,flush=True)
