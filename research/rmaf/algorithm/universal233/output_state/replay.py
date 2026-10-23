#!/usr/bin/env python3
"""One-shot source-bound output-state AUTHOR replay, adapted from completed
restriction/group/binary replayers. Full isolated origins and standard axioms;
no fresh nonauthor acceptance is asserted by this script.
"""
from pathlib import Path
import hashlib,json,re,os,subprocess,time,datetime
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent
STAMP=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT=R/'results'/('algorithm-universal233-output-state-'+STAMP);OUT.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def clean(s):
 s=re.sub(r'/\-.*?\-/','',s,flags=re.S);return re.sub(r'--[^\n]*','',s)
stack=json.loads((D/'STACK-PINS.json').read_text());binary=json.loads((D/'BINARY-STACK-PINS.json').read_text())
checks=stack['manifests']+[binary['manifest']]
for c in checks:
 p=R/c['path'];pin(p,c['sha256']);m=json.loads(p.read_text());rows=m.get('immutable_files',m.get('entries',[]));assert rows
 for e in rows:pin(R/e['path'],e['sha256'])
entries=stack['entries']+binary['entries']
local=['OutputDefs','OutputControls','Materialize','Equivalence','Permutation','OppositeGroups','LocalCertificates','ResidualConsumer','ActualConsumers']
for n in local:
 p=D/(n+'.lean');entries.append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),adaptations={},adapted_sha256=sha(p)))
order=[e['module'] for e in entries];assert len(order)==len(set(order))
pre=json.loads((D/'PREPROOF-RECEIPT-v1.json').read_text());assert pre['status']=='PASS_PREPROOF'
for n,h in pre['files'].items():pin(D/n,h)
inputs={str((D/n).relative_to(R)):sha(D/n) for n in ['TARGET-v1.md','CONTROLS-PIN-v1.json','PREPROOF-RECEIPT-v1.json','FalseOutputControls.lean','prepare.py','extend_binary.py','precontrols.py','replay.py','STACK-PINS.json','BINARY-STACK-PINS.json']}
for e in entries:
 p=R/e['path'];pin(p,e['sha256']);src=p.read_text()
 for old,new in e['adaptations'].items():
  assert src.count('import '+old+'\n')==1;src=src.replace('import '+old+'\n','import '+new+'\n',1)
 assert hashlib.sha256(src.encode()).hexdigest()==e['adapted_sha256']
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(src)),e['path']
 (OUT/(e['module']+'.lean')).write_text(src)
for n in ['FalseOutputControls.lean','TARGET-v1.md','CONTROLS-PIN-v1.json','PREPROOF-RECEIPT-v1.json']:(OUT/n).write_bytes((D/n).read_bytes())
(OUT/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
record=dict(status='RUNNING_AUTHOR',all_three_main_milestones='OPEN',fresh_nonauthor_acceptance=False,full_solver=False,runtime_theorem=False,novelty_claim=False,source_inputs=entries,positive_order=order,upstream_manifests=checks,development_aliases=binary['aliases'],input_hashes=inputs,preproof_receipt_sha256=sha(D/'PREPROOF-RECEIPT-v1.json'),runs=[],controls={})
def save():(OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def run(n,build=False):
 t=time.monotonic();p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(OUT/(n+'.olean'))] if build else [])+[str(OUT/(n+'.lean'))],cwd=OUT,env=dict(os.environ,LEAN_PATH=str(OUT)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (OUT/(n+'.log')).write_text(p.stdout);record['runs'].append(dict(module=n,exit=p.returncode,seconds=round(time.monotonic()-t,6)));save();return p
for wrapper in ['bootloops-lean','bootloops-lake']:
 p=subprocess.run([str(R/wrapper),'--version'],cwd=OUT,env=dict(os.environ,LEAN_PATH=str(OUT)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 assert p.returncode==0;(OUT/(wrapper+'-version.log')).write_text(p.stdout);record[wrapper+'_version']=p.stdout.strip()
(OUT/'TrueControl.lean').write_text('import Std\nexample : (2 : Nat)+3=5 := by decide\n')
(OUT/'FalseControl.lean').write_text('import Std\nexample : (2 : Nat)+3=6 := by decide\n')
assert run('TrueControl').returncode==0
p=run('FalseControl');assert p.returncode!=0 and p.stdout.count('is false')==1
record['controls'].update(known_true='ACCEPTED',known_false='REJECTED')
for n in order:
 p=run(n,True);assert p.returncode==0 and not re.search(r'error:|sorryAx|declaration uses .sorry.',p.stdout),(n,p.stdout)
p=run('FalseOutputControls');assert p.returncode!=0 and p.stdout.count('is false')==4,p.stdout
record['controls']['actual_false_claims']='REJECTED_4_OF_4'
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
actual=p.stdout
ALLOWED={'propext','Quot.sound','Classical.choice'}
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
for label,corrupt in [('missing_axiom_record',re.sub(r'^MODAUDIT\|[^\n]+\n','',actual,count=1,flags=re.M)),('wrong_module_path',re.sub(r'^PATH\|Equivalence\|[^\n]+','PATH|Equivalence|/tmp/foreign.olean',actual,flags=re.M)),('wrong_module_origin',re.sub(r'^MODULE\|Equivalence\|','MODULE|ForeignModule|',actual,count=1,flags=re.M))]:
 try:parse(corrupt)
 except AssertionError as err:record['controls'][label]='CAUGHT: '+str(err)
 else:raise AssertionError('corruption survived: '+label)
(OUT/'ForeignPrivate.lean').write_text('namespace UnrelatedNamespace\nprivate axiom concealed : False\ntheorem use_concealed : False := concealed\nend UnrelatedNamespace\n')
assert run('ForeignPrivate',True).returncode==0
(OUT/'ForeignAudit.lean').write_text(inventory('ForeignPrivate'));p=run('ForeignAudit');assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM' in p.stdout,p.stdout
record['controls']['hidden_private_custom_axiom']='CAUGHT_BY_ACTUAL_MODULE_ORIGIN'
p=OUT/'CorruptionFixture.txt';p.write_bytes((D/'Equivalence.lean').read_bytes());h=sha(p);pin(p,h);p.write_bytes(p.read_bytes()+b'\n-- deliberate source-byte corruption\n')
try:pin(p,h)
except ValueError as err:record['controls']['source_byte_corruption']='CAUGHT_WITH_CLEAN_TWIN'
else:raise AssertionError('source byte corruption survived')
p.write_bytes((D/'Equivalence.lean').read_bytes());pin(p,h)
for e in entries:
 pin(R/e['path'],e['sha256']);pin(OUT/(e['module']+'.lean'),e['adapted_sha256'])
for rel,h in inputs.items():pin(R/rel,h)
assert any('_private' in n and 'actual_private_origin' in n for _,n in mm),'private source declarations omitted'
record.update(status='PASS_AUTHOR_SOURCE_BOUND_REPLAY',positive_source_modules=len(order),module_origin_declarations=len(mm),module_counts={m:sum(x==m for x,_ in mm) for m in order},resolved_module_paths=paths,standard_axioms_observed=union,private_generated_declarations_included=True,literal_equivalence=True,source_Q_only=True,exact_additional_cost=True,actual_opposite_grouping=True,actual_A_one_C_zero=True,whole_Bforest_residual_query=True)
record['module_inventory_sha256']=sha(OUT/'ModuleAudit.log');save()
(OUT/'VERDICT.txt').write_text(f'PASS AUTHOR SOURCE-BOUND REPLAY: {len(order)} modules; {len(mm)} actual module-origin declarations; standard axioms only. Actual true/false controls and all audit/source plants caught. Fresh nonauthor acceptance and all three main milestones OPEN.\n')
(D/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
print('PASS AUTHOR',len(order),'source modules;',len(mm),'module-origin declarations; controls',record['controls']);print('Receipt',OUT)
