#!/usr/bin/env python3
"""One-task isolated full-source AUTHOR replay. No independent acceptance claim."""
from pathlib import Path
import hashlib,json,re,os,subprocess,time,datetime
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent
STAMP=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
OUT=R/'results'/('algorithm-universal233-forest-solver-'+STAMP);OUT.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def clean(s):
 s=re.sub(r'/\-.*?\-/','',s,flags=re.S);return re.sub(r'--[^\n]*','',s)
entries=[]
for f in ['STACK-PINS.json','MAF-PINS.json','WORK-PINS.json']:entries+=json.loads((D/f).read_text())['entries']
local=['ForestDefs','ForestPrecontrols','ForestReplace','ForestOverlap','ForestReverse','ForestProgram','ForestSelection','ForestProgramControls','ForestConditional','ForestQueries','ForestLocal','ForestDisjointPlan','ForestDisjoint','ForestWork','ForestWorkBound','ForestTrace','ForestResource']
for n in local:
 p=D/(n+'.lean');entries.append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),adaptations={},adapted_sha256=sha(p)))
order=[e['module'] for e in entries];assert len(order)==len(set(order))
pre=json.loads((D/'PREPROOF-RECEIPT-v1.json').read_text());assert pre['status']=='PASS_PREPROOF'
for n,h in pre['files'].items():pin(D/n,h)
checks=json.loads((U/'output_state/STACK-PINS.json').read_text())['manifests']+[json.loads((U/'output_state/BINARY-STACK-PINS.json').read_text())['manifest']]
for p in [U/'maf_scheduler/MAF-SCHEDULER-MANIFEST-v1.json',U/'core_work/CORE-WORK-MANIFEST-v1.json',U/'whole_source_work/WHOLE-SOURCE-WORK-MANIFEST-v1.json']:
 checks.append(dict(path=str(p.relative_to(R)),sha256=sha(p)))
for check in checks:
 p=R/check['path'];pin(p,check['sha256']);m=json.loads(p.read_text());rows=m.get('immutable_files',m.get('entries',[]));assert rows,p
 for e in rows:pin(R/e['path'],e['sha256'])
inputs={str((D/n).relative_to(R)):sha(D/n) for n in ['TARGET-v1.md','CONTROLS-PIN-v1.json','PREPROOF-RECEIPT-v1.json','FalseForestControls.lean','prepare.py','precontrols.py','extend_maf.py','extend_work.py','replay.py','STACK-PINS.json','MAF-PINS.json','WORK-PINS.json','README.md','RESULT.md','FIRST-GAP.md','SOURCE-WORK.md','INTERFACE.md']}
for e in entries:
 p=R/e['path'];pin(p,e['sha256']);s=p.read_text()
 for old,new in e['adaptations'].items():
  assert s.count('import '+old+'\n')==1;s=s.replace('import '+old+'\n','import '+new+'\n',1)
 assert hashlib.sha256(s.encode()).hexdigest()==e['adapted_sha256']
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(s)),e['path']
 (OUT/(e['module']+'.lean')).write_text(s)
for n in ['FalseForestControls.lean','TARGET-v1.md','CONTROLS-PIN-v1.json','PREPROOF-RECEIPT-v1.json','FIRST-GAP.md','SOURCE-WORK.md','INTERFACE.md']:(OUT/n).write_bytes((D/n).read_bytes())
(OUT/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
record=dict(status='RUNNING_AUTHOR',all_three_main_milestones='OPEN',fresh_nonauthor_acceptance=False,full_ordinary_tree_algorithm=False,unconditional_runtime=False,novelty_claim=False,ordinary_only_conditional_exact=True,qualified_source_bill_bound=True,source_inputs=entries,positive_order=order,upstream_manifests=checks,input_hashes=inputs,preproof_receipt_sha256=sha(D/'PREPROOF-RECEIPT-v1.json'),runs=[],controls={})
def save():(OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def run(n,build=False):
 t=time.monotonic();p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(OUT/(n+'.olean'))] if build else [])+[str(OUT/(n+'.lean'))],cwd=OUT,env=dict(os.environ,LEAN_PATH=str(OUT)),capture_output=True,text=True,timeout=60)
 p.stdout+=p.stderr;(OUT/(n+'.log')).write_text(p.stdout);record['runs'].append(dict(module=n,exit=p.returncode,seconds=round(time.monotonic()-t,6)));save();return p
for wrapper in ['bootloops-lean','bootloops-lake']:
 p=subprocess.run([str(R/wrapper),'--version'],cwd=OUT,env=dict(os.environ,LEAN_PATH=str(OUT)),capture_output=True,text=True,timeout=30)
 assert p.returncode==0;(OUT/(wrapper+'-version.log')).write_text(p.stdout+p.stderr);record[wrapper+'_version']=p.stdout.strip()
(OUT/'TrueControl.lean').write_text('import Std\nexample : (2 : Nat)+3=5 := by decide\n')
(OUT/'FalseControl.lean').write_text('import Std\nexample : (2 : Nat)+3=6 := by decide\n')
assert run('TrueControl').returncode==0
p=run('FalseControl');assert p.returncode!=0 and p.stdout.count('is false')==1
record['controls'].update(known_true='ACCEPTED',known_false='REJECTED')
for n in order:
 p=run(n,True);assert p.returncode==0 and not re.search(r'error:|sorryAx|declaration uses .sorry.',p.stdout),(n,p.stdout)
p=run('FalseForestControls');assert p.returncode!=0 and p.stdout.count('is false')==2,p.stdout
record['controls']['actual_false_extensions']='REJECTED_2_OF_2'
def inventory(extra=None):
 mods=order+([extra] if extra else []);imports='\n'.join('import '+n for n in mods);names=', '.join('`'+n for n in mods)
 return imports+'''\nimport Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := ['''+names+''']
 for mod in env.header.moduleNames do
   let path ← liftIO <| findOLean mod
   logInfo m!"PATH|{mod}|{path}"
 let ns := (((env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)).filter fun n =>
   match env.getModuleIdxFor? n with
   | some i => mods.contains env.header.moduleNames[i.toNat]!
   | none => false).eraseDups
 for n in ns do
   let some i := env.getModuleIdxFor? n | throwError "missing module origin"
   logInfo m!"MODULE|{env.header.moduleNames[i.toNat]!}|{n}"
   let axs ← collectAxioms n
   logInfo m!"MODAUDIT|{n}|{String.intercalate "," (axs.toList.map toString)}"
   for ax in axs do
     unless ax == `propext || ax == `Quot.sound || ax == `Classical.choice do
       throwError m!"REJECT_CUSTOM_AXIOM|{n}|{ax}"
'''
(OUT/'ModuleAudit.lean').write_text(inventory());p=run('ModuleAudit');assert p.returncode==0,p.stdout
actual=p.stdout;ALLOWED={'propext','Quot.sound','Classical.choice'}
def parse(s):
 mm=re.findall(r'^MODULE\|([^|]+)\|(.+)$',s,re.M);aa=re.findall(r'^MODAUDIT\|([^|\n]+)\|([^\n]*)$',s,re.M);paths=dict(re.findall(r'^PATH\|([^|]+)\|(.+)$',s,re.M))
 assert mm and len(mm)==len(aa)==len(set(mm)) and {n for _,n in mm}=={n for n,_ in aa},'incomplete/duplicate origin-axiom inventory'
 assert {m for m,_ in mm}==set(order),'missing/extra source module origin'
 for mod,raw in paths.items():
  path=Path(raw).resolve()
  if mod in order:assert path==OUT/(mod+'.olean'),'wrong local module path: '+mod
  else:assert path.is_relative_to(R/'.runtime/elan/toolchains'),'non-toolchain dependency: '+str(path)
 assert set(order)<=set(paths),'missing source module path'
 union={x.strip() for _,a in aa for x in a.split(',') if x.strip()};assert union<=ALLOWED,'custom axiom'
 return mm,aa,paths,sorted(union)
mm,aa,paths,union=parse(actual)
for label,corrupt in [('missing_axiom_record',re.sub(r'^MODAUDIT\|[^\n]+\n','',actual,count=1,flags=re.M)),('wrong_module_path',re.sub(r'^PATH\|ForestDisjoint\|[^\n]+','PATH|ForestDisjoint|/tmp/foreign.olean',actual,flags=re.M)),('wrong_module_origin',re.sub(r'^MODULE\|ForestDisjoint\|','MODULE|ForeignModule|',actual,count=1,flags=re.M))]:
 try:parse(corrupt)
 except AssertionError as err:record['controls'][label]='CAUGHT: '+str(err)
 else:raise AssertionError('corruption survived: '+label)
(OUT/'ForeignPrivate.lean').write_text('namespace UnrelatedNamespace\nprivate axiom concealed : False\ntheorem use_concealed : False := concealed\nend UnrelatedNamespace\n')
assert run('ForeignPrivate',True).returncode==0
(OUT/'ForeignAudit.lean').write_text(inventory('ForeignPrivate'));p=run('ForeignAudit');assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM' in p.stdout,p.stdout
record['controls']['hidden_private_custom_axiom']='CAUGHT_BY_ACTUAL_MODULE_ORIGIN'
p=OUT/'CorruptionFixture.txt';p.write_bytes((D/'ForestDisjoint.lean').read_bytes());h=sha(p);pin(p,h);p.write_bytes(p.read_bytes()+b'\n-- deliberate source-byte corruption\n')
try:pin(p,h)
except ValueError as err:record['controls']['source_byte_corruption']='CAUGHT_WITH_CLEAN_TWIN'
else:raise AssertionError('source byte corruption survived')
p.write_bytes((D/'ForestDisjoint.lean').read_bytes());pin(p,h)
for e in entries:
 pin(R/e['path'],e['sha256']);pin(OUT/(e['module']+'.lean'),e['adapted_sha256'])
for rel,h in inputs.items():pin(R/rel,h)
for check in checks:
 p=R/check['path'];pin(p,check['sha256']);m=json.loads(p.read_text());rows=m.get('immutable_files',m.get('entries',[]))
 for e in rows:pin(R/e['path'],e['sha256'])
assert any('_private' in n and 'actual_private_origin' in n for _,n in mm),'private source declarations omitted'
record.update(status='PASS_AUTHOR_SOURCE_BOUND_REPLAY',positive_source_modules=len(order),module_origin_declarations=len(mm),module_counts={m:sum(x==m for x,_ in mm) for m in order},resolved_module_paths=paths,standard_axioms_observed=union,private_generated_declarations_included=True,local_authored_modules=len(local),local_declarations=sum(m in local for m,_ in mm))
record['module_inventory_sha256']=sha(OUT/'ModuleAudit.log');save()
(OUT/'VERDICT.txt').write_text(f'PASS AUTHOR SOURCE-BOUND REPLAY: {len(order)} modules; {len(mm)} actual module-origin declarations; standard axioms only. Conditional exact generic forest minimum from ordinary IH; qualified source bill bound. Fresh nonauthor acceptance and all three main milestones OPEN.\n')
(D/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
print('PASS AUTHOR',len(order),'source modules;',len(mm),'module-origin declarations; local',record['local_declarations']);print('Receipt',OUT)
