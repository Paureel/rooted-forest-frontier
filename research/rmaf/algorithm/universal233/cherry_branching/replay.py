#!/usr/bin/env python3
"""One-shot exact source-bound ordinary cherry AUTHOR replay.
No fresh nonauthor acceptance; after freeze creates only new results evidence.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent
O=R/'results'/('algorithm-universal233-cherry-branch-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir()
ENV=dict(os.environ,LEAN_PATH=str(O));ALLOWED={'Classical.choice','propext','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def clean(s):
 s=re.sub(r'/\-.*?\-/','',s,flags=re.S);return re.sub(r'--[^\n]*','',s)
MANIFEST=D/'CHERRY-BRANCH-MANIFEST-v1.json'
if MANIFEST.exists():
 for e in json.loads(MANIFEST.read_text())['immutable_files']:pin(R/e['path'],e['sha256'])
entries=json.loads((D/'DEV-STACK.json').read_text());order=[e['module'] for e in entries]
assert len(order)==len(set(order))
frozen={};upstreams=[]
for rel in ['hard_parent_refinement/HARD-PARENT-REFINEMENT-MANIFEST-v1.json','output_state/OUTPUT-STATE-MANIFEST-v1.json','state_cherry_completion/CHERRY-MANIFEST-v1.json']:
 p=U/rel;x=json.loads(p.read_text());upstreams.append(dict(path=str(p.relative_to(R)),sha256=sha(p)))
 rows=x.get('immutable_files',[])
 if rows:
  for e in rows:pin(R/e['path'],e['sha256']);frozen[e['path']]=e['sha256']
 else:
  for path,h in x['exact_source_import_pins'].items():pin(R/path,h);frozen[path]=h
# Exact transitive dependency manifests are part of the completed output-state
# development record; validate them before accepting their original sources.
stack=json.loads((U/'output_state/STACK-PINS.json').read_text())
binary=json.loads((U/'output_state/BINARY-STACK-PINS.json').read_text())
for e in stack['manifests']+[binary['manifest']]:
 p=R/e['path'];pin(p,e['sha256']);x=json.loads(p.read_text())
 upstreams.append(dict(path=e['path'],sha256=sha(p)))
 for row in x['immutable_files']:pin(R/row['path'],row['sha256']);frozen[row['path']]=row['sha256']
assert sha(U/'state_cherry_completion/CHERRY-MANIFEST-v1.json')=='b9d584872792f5d6b8c00509c56160c47ac62732ef9a44f7c21c3b5717d53147'
pre=json.loads((D/'PREPROOF-RECEIPT-v1.json').read_text());pin(R/pre['receipt']/'certificate.json',pre['sha256'])
for rel,h in pre['source_hashes'].items():pin(R/rel,h)
assert json.loads((R/pre['receipt']/'certificate.json').read_text())['status']=='PASS_PREPROOF'
record=dict(status='RUNNING_AUTHOR',all_three_main_milestones='OPEN',fresh_nonauthor_acceptance=False,full_solver=False,full_runtime=False,novelty_claim=False,source_entries=entries,upstream_manifests=upstreams,preproof=pre,runs=[],controls={},input_hashes={})
def save():(O/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
for e in entries:
 p=R/e['path'];pin(p,e['sha256']);src=p.read_text()
 if not p.is_relative_to(D):assert frozen.get(e['path'])==e['sha256'],'UNFROZEN_DEVELOPMENT_SOURCE|'+e['path']
 for old,new in e.get('adaptations',{}).items():src=src.replace('import '+old+'\n','import '+new+'\n')
 assert hashlib.sha256(src.encode()).hexdigest()==e['adapted_sha256']
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(src)),e['path']
 (O/(e['module']+'.lean')).write_text(src)
for p in list(D.glob('*.md'))+[D/n for n in ['FalseControls.lean','FalsePreControls.lean','PREPROOF-RECEIPT-v1.json','DEV-STACK.json','lean-toolchain','precontrols.py','devbuild.py','replay.py','freeze.py']]:
 record['input_hashes'][str(p.relative_to(R))]=sha(p)
 if p.suffix in ['.md','.lean'] or p.name=='lean-toolchain':(O/p.name).write_bytes(p.read_bytes())
record['input_hashes'].update({str((R/n).relative_to(R)):sha(R/n) for n in ['bootloops-lean','bootloops-lake','bootloops-python']})
(O/'lean-toolchain').write_bytes((D/'lean-toolchain').read_bytes());save()
def run(n,build=False):
 t=time.monotonic();p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(O/(n+'.olean'))] if build else [])+[str(O/(n+'.lean'))],cwd=O,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (O/(n+'.log')).write_text(p.stdout);record['runs'].append(dict(module=n,exit=p.returncode,seconds=round(time.monotonic()-t,6)));save();return p
for n in ['bootloops-lean','bootloops-lake']:
 p=subprocess.run([str(R/n),'--version'],cwd=O,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);assert p.returncode==0
 (O/(n+'-version.log')).write_text(p.stdout)
(O/'TrueControl.lean').write_text('import Std\nexample : (2 : Nat)+3=5 := by decide\n')
(O/'FalseControl.lean').write_text('import Std\nexample : (2 : Nat)+3=6 := by decide\n')
assert run('TrueControl').returncode==0
p=run('FalseControl');assert p.returncode!=0 and p.stdout.count('is false')==1
record['controls'].update(true_control='ACCEPTED',false_control='REJECTED')
start=time.monotonic()
for n in order:
 p=run(n,True);assert p.returncode==0 and not re.search(r'error:|sorryAx|declaration uses .sorry.',p.stdout),(n,p.stdout)
for n in ['FalsePreControls','FalseControls']:
 p=run(n);assert p.returncode!=0 and p.stdout.count('is false')==5,(n,p.stdout)
 record['controls'][n]='REJECTED_5_OF_5'
def inventory(extra=None):
 mods=order+([extra] if extra else [])
 return '\n'.join('import '+n for n in mods)+'''\nimport Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := ['''+', '.join('`'+n for n in mods)+''']
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
   for a in axs do
     unless a == `propext || a == `Quot.sound || a == `Classical.choice do
       throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
'''
(O/'ModuleAudit.lean').write_text(inventory());p=run('ModuleAudit');assert p.returncode==0,p.stdout
def parse(s):
 mm=re.findall(r'^MODULE\|([^|]+)\|(.+)$',s,re.M);aa=re.findall(r'^MODAUDIT\|([^|\n]+)\|([^\n]*)$',s,re.M);paths=dict(re.findall(r'^PATH\|([^|]+)\|(.+)$',s,re.M))
 assert mm and len(mm)==len(aa)==len(set(mm)) and {n for _,n in mm}=={n for n,_ in aa},'INCOMPLETE_OR_DUPLICATE_AUDIT'
 assert {m for m,_ in mm}==set(order),'MISSING_SOURCE_MODULE_ORIGIN'
 for mod,raw in paths.items():
  path=Path(raw).resolve()
  if mod in order:assert path==O/(mod+'.olean'),'WRONG_LOCAL_MODULE_PATH'
  else:assert path.is_relative_to(R/'.runtime/elan/toolchains'),'NON_TOOLCHAIN_DEPENDENCY'
 assert set(order)<=set(paths),'MISSING_SOURCE_MODULE_PATH'
 union={z.strip() for _,v in aa for z in v.split(',') if z.strip()};assert union<=ALLOWED,'CUSTOM_AXIOM'
 assert any(m=='Controls' and '_private' in n and 'internal_control' in n for m,n in mm),'MISSING_PRIVATE_CONTROL'
 return mm,aa,paths,union
actual=p.stdout;mm,aa,paths,axs=parse(actual)
for tag,mutant in [('missing_audit_row',re.sub(r'^MODAUDIT\|[^\n]+\n','',actual,count=1,flags=re.M)),('wrong_local_path',actual.replace('PATH|RMAF|'+str(O/'RMAF.olean'),'PATH|RMAF|/tmp/foreign/RMAF.olean',1))]:
 try:parse(mutant)
 except AssertionError:record['controls'][tag]='CAUGHT'
 else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
(O/'AuditPlant.lean').write_text('namespace OutsideExpected\nprivate axiom concealed : False\nprivate theorem touched : False := concealed\nend OutsideExpected\n')
assert run('AuditPlant',True).returncode==0
(O/'PlantAudit.lean').write_text(inventory('AuditPlant'));p=run('PlantAudit')
assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM|' in p.stdout and 'concealed' in p.stdout
record['controls']['hidden_private_custom_axiom']='CAUGHT'
try:pin(R/entries[0]['path'],'0'*64)
except ValueError:record['controls']['source_pin_corruption']='CAUGHT'
else:raise AssertionError('SOURCE_PIN_CORRUPTION_SURVIVED')
keys=['actual_t1_pendant_exchange','actual_t1_unordered_exchange','actual_t1_target','actual_t1_two_minimum','actual_t1_deterministic_minimum','actual_t1_two_budget','actual_t1_decision','actual_high_safety','actual_high_unordered_safety','actual_high_budget','ordinary_minimum','high_child_solver_iff','t1_child_solver_iff','core_has_cherry','split_original_agreement','state_save_singleton','cut_component','root_component','original_cover','roots_separated','cut_leafset','root_leafset','no_leafless','pendant_partition_check','source_embeddings','partition_length','selected_spec','selected_actual','endpoint_literal','endpoint_components','forest_length','paid_budget_identity','remaining_correct']
(O/'Interfaces.lean').write_text('import Controls\n'+''.join('#check Universal233.CherryBranching.'+n+'\n' for n in keys))
p=run('Interfaces');assert p.returncode==0,p.stdout
for e in entries:pin(R/e['path'],e['sha256'])
for rel,h in record['input_hashes'].items():pin(R/rel,h)
record.update(status='PASS_AUTHOR_KERNEL',local_claims='t1 no-larger original exchange and safe two/deterministic branches; high source refinement and literal (1,1,t) branches',source_builds=len(order),module_origin_declarations=len(mm),axiom_union=sorted(axs),private_generated_included=True,module_counts={m:sum(a==m for a,_ in mm) for m in order},origin_inventory=[dict(module=m,name=n) for m,n in mm],axioms_by_declaration={n:[z.strip() for z in v.split(',') if z.strip()] for n,v in aa},interfaces=keys,seconds_measured=time.monotonic()-start,qualified_source_work='inspection argument in SOURCE-WORK.md; no extracted fine-operation bound',skipped='No toolkit-wide suite; no independent verification; no global solver/runtime/novelty claim')
save()
verdict=f'PASS_AUTHOR_KERNEL: {len(order)} isolated source modules; {len(mm)} full module-origin audits; 10 rejected actual false claims; 4 caught pin/audit/path/axiom corruptions'
(O/'VERDICT.txt').write_text(verdict+'\nAll three global milestones OPEN; fresh nonauthor acceptance pending.\n')
(O/'SOURCE-PINS.json').write_text(json.dumps({e['path']:e['sha256'] for e in entries},indent=2)+'\n')
files={p.name:dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(O.iterdir()) if p.is_file()}
(O/'RECEIPT-FILES.json').write_text(json.dumps(files,indent=2)+'\n')
for p in O.iterdir():
 if p.is_file():p.chmod(0o444)
O.chmod(0o555)
print(verdict);print(O)
