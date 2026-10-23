#!/usr/bin/env python3
"""One-shot source-bound isolated forest-group author replay.

Reuses the completed state/restriction inventory procedure; expected mathematical
values remain the handwritten preproof controls. This author run cannot supply
fresh nonauthor mathematical acceptance.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BASE=HERE.parent
STAMP=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
OUT=ROOT/'results'/('algorithm-universal233-forest-groups-'+STAMP)
OUT.mkdir(parents=True,exist_ok=False)
if not (HERE/'FOREST-GROUPS-MANIFEST-v1.json').exists():
 (HERE/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
DEPS=json.loads((HERE/'STACK-PINS.json').read_text())['entries']
LOCAL=['GroupControls','GroupDefs','GroupForwardProof','GroupReverseProof','GroupCostProof','GroupPriority','GroupConsumerControls']
MODS=[r['module'] for r in DEPS]+LOCAL
ALLOWED={'propext','Quot.sound','Classical.choice'}
ENV=dict(os.environ,LEAN_PATH=str(OUT))
record=dict(status='RUNNING',grade='AUTHOR_KERNEL_REPLAY_ONLY',all_three_main_milestones='OPEN',
 fresh_nonauthor_acceptance=False,full_algorithm='OPEN',novelty='NOT_CLAIMED',builds=[],controls={},input_hashes={},adaptations=[])

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save():(OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def pin(path):record['input_hashes'][str(path.relative_to(ROOT))]=sha(path)
def clean(s):
 s=re.sub(r'/\-.*?\-/',lambda m:'\n'*m.group().count('\n'),s,flags=re.S)
 return re.sub(r'--[^\n]*','',s)
def run(n,build=False):
 args=[str(ROOT/'bootloops-lean')]
 if build:args+=['-o',str(OUT/(n+'.olean'))]
 args += [str(OUT/(n+'.lean'))]
 start=time.monotonic()
 p=subprocess.run(args,cwd=OUT,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (OUT/(n+'.log')).write_text(p.stdout)
 record['builds'].append(dict(module=n,returncode=p.returncode,seconds=round(time.monotonic()-start,6)))
 save();return p

def require_sha(path,expected):
 assert sha(path)==expected,'source pin mismatch: '+str(path)

# Every development dependency must also match an actually frozen input.
FROZEN={}
for rel in ['state_reductions/STATE-MANIFEST-v1.json','restriction_bridge/RESTRICTION-MANIFEST-v1.json','depth_one/DEPTH-ONE-MANIFEST-v1.json']:
 p=BASE/rel;pin(p)
 d=json.loads(p.read_text())
 for r in d['immutable_files']:FROZEN[r['path']]=r['sha256']
 FROZEN.update(d.get('dependency_source_hashes',{}))
for r in DEPS:
 p=ROOT/r['path'];require_sha(p,r['sha256'])
 assert FROZEN.get(r['path'])==r['sha256'],'dependency absent from frozen permitted manifests: '+r['path']
 s=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(s)),str(p)
 for old,new in r['adaptations'].items():
  assert s.count('import '+old+'\n')==1
  s=s.replace('import '+old+'\n','import '+new+'\n',1)
 assert hashlib.sha256(s.encode()).hexdigest()==r['adapted_sha256']
 (OUT/(r['module']+'.lean')).write_text(s);pin(p)
 record['adaptations'].append(r)
for n in LOCAL:
 p=HERE/(n+'.lean');s=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(s)),str(p)
 (OUT/(n+'.lean')).write_bytes(p.read_bytes());pin(p)
for n in ['TARGET-v1.md','CONTROLS-v1.md','CONTROLS-PIN-v1.json','FalseGroupControls.lean','STACK-PINS.json','FIRST-GAP.md','RUNTIME.md','INTERFACE.md','RESULT.md','README.md','WORKFILE.md','PROSE-CHECK.md','AUTHOR-CHECKS-v1.md']:
 p=HERE/n;pin(p);(OUT/n).write_bytes(p.read_bytes())
for p in [Path(__file__),HERE/'prepare.py',HERE/'precontrols.py',HERE/'dev.py',ROOT/'bootloops-lean',ROOT/'bootloops-lake',ROOT/'bootloops-python']:pin(p)
(OUT/'preproof-controls-receipt.json').write_bytes((HERE/'build/preproof-controls-receipt.json').read_bytes())
pre=json.loads((OUT/'preproof-controls-receipt.json').read_text())
assert pre['status']=='PASS_PREPROOF'
require_sha(HERE/'CONTROLS-PIN-v1.json',pre['pin_sha256'])
record['preproof_controls_receipt_sha256']=sha(OUT/'preproof-controls-receipt.json')
for rel,digest in json.loads((HERE/'CONTROLS-PIN-v1.json').read_text())['pins'].items():require_sha(ROOT/rel,digest)
(OUT/'lean-toolchain').write_bytes((BASE/'integration/lean-toolchain').read_bytes())
for wrapper in ['bootloops-lean','bootloops-lake']:
 p=subprocess.run([str(ROOT/wrapper),'--version'],cwd=OUT,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (OUT/(wrapper+'-version.log')).write_text(p.stdout);assert p.returncode==0
 record[wrapper+'_version']=p.stdout.strip()
(OUT/'TrueControl.lean').write_text('import Std\nexample : (2 : Nat) + 3 = 5 := by decide\n')
(OUT/'FalseControl.lean').write_text('import Std\nexample : (2 : Nat) + 3 = 6 := by decide\n')
assert run('TrueControl').returncode==0
p=run('FalseControl');assert p.returncode!=0 and 'is false' in p.stdout
record['controls'].update(known_true='ACCEPTED',known_false='REJECTED')
for n in MODS:
 p=run(n,True)
 assert p.returncode==0 and not re.search(r'error:|sorryAx|declaration uses .sorry.',p.stdout),(n,p.stdout)
 if n=='GroupControls':
  p=run('FalseGroupControls')
  assert p.returncode!=0 and p.stdout.count('is false')==3,p.stdout
  record['controls']['three_pinned_false_propositions']='REJECTED_3_OF_3'

inventory='''import GroupConsumerControls
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [MODULES]
  for mod in env.header.moduleNames do
    let path ← liftIO <| findOLean mod
    logInfo m!"PATH|{mod}|{path}"
  let ns := (env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)
  let ns := (ns.filter fun n =>
    match env.getModuleIdxFor? n with
    | some idx => modules.contains env.header.moduleNames[idx.toNat]!
    | none => false).eraseDups
  for n in ns do
    let some idx := env.getModuleIdxFor? n | throwError "missing module origin"
    let mod := env.header.moduleNames[idx.toNat]!
    logInfo m!"MODULE|{mod}|{n}"
  for n in ns do
    let axs ← collectAxioms n
    logInfo m!"MODAUDIT|{n}|{String.intercalate "," (axs.toList.map toString)}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
'''.replace('MODULES',', '.join('`'+n for n in MODS))
(OUT/'ModuleInventory.lean').write_text(inventory)
p=run('ModuleInventory');assert p.returncode==0,p.stdout

def parse(s):
 origins=re.findall(r'^MODULE\|([^|]+)\|(.+)$',s,re.M)
 axioms=re.findall(r'^MODAUDIT\|([^|]+)\|([^\n]*)$',s,re.M)
 assert origins and len(origins)==len(axioms)==len(set(origins)),'incomplete/duplicate declaration inventory'
 assert {n for _,n in origins}=={n for n,_ in axioms},'missing axiom declaration'
 assert {m for m,_ in origins}==set(MODS),'missing/extra source module origin'
 pathrows=re.findall(r'^PATH\|([^|]+)\|(.+)$',s,re.M)
 assert len(pathrows)==len(dict(pathrows)),'duplicate resolved module path'
 paths=dict(pathrows)
 for mod,rawpath in paths.items():
  path=Path(rawpath).resolve()
  if mod in MODS:assert path==OUT/(mod+'.olean'),'wrong local module path: '+mod
  else:assert path.is_relative_to(ROOT/'.runtime/elan/toolchains'),'foreign imported dependency: '+str(path)
 for mod in MODS:assert mod in paths,'missing source module path: '+mod
 for n,axs in axioms:
  assert set(filter(None,axs.split(',')))<=ALLOWED,'nonstandard axiom row: '+n
 return origins,axioms,paths
origins,axioms,paths=parse(p.stdout)
for label,bad in [
 ('missing_axiom_record',re.sub(r'^MODAUDIT\|[^\n]+\n','',p.stdout,count=1,flags=re.M)),
 ('wrong_module_path',re.sub(r'^PATH\|GroupRestriction\|[^\n]+','PATH|GroupRestriction|/tmp/foreign.olean',p.stdout,flags=re.M)),
 ('wrong_module_origin',re.sub(r'^MODULE\|GroupDefs\|','MODULE|ForeignModule|',p.stdout,count=1,flags=re.M)),
 ('nonstandard_axiom_record',re.sub(r'^(MODAUDIT\|[^|]+\|)[^\n]*',r'\1Hidden.bad',p.stdout,count=1,flags=re.M))]:
 try:parse(bad)
 except AssertionError as err:record['controls'][label]='CAUGHT: '+str(err)
 else:raise AssertionError('corruption survived: '+label)
record['module_origin_counts']={n:sum(m==n for m,_ in origins) for n in MODS}
record['module_origin_total']=len(origins)
record['resolved_module_paths']=paths
record['axiom_union_observed']=sorted({a for _,xs in axioms for a in xs.split(',') if a})
(OUT/'PlantModel.lean').write_text('namespace HiddenForestGroupPlant\naxiom borrowed : False\nend HiddenForestGroupPlant\n')
assert run('PlantModel',True).returncode==0
(OUT/'ModulePlantAudit.lean').write_text('import PlantModel\n'+inventory.replace('`GroupConsumerControls]','`GroupConsumerControls, `PlantModel]'))
p=run('ModulePlantAudit')
assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM|HiddenForestGroupPlant.borrowed|HiddenForestGroupPlant.borrowed' in p.stdout,p.stdout
record['controls']['hidden_custom_axiom']='CAUGHT'
corrupt=OUT/'GroupReverseProof-corrupted.txt'
corrupt.write_bytes((OUT/'GroupReverseProof.lean').read_bytes()+b'\n-- deliberate source corruption\n')
for label,path,digest in [('source_byte_corruption',corrupt,sha(HERE/'GroupReverseProof.lean')),('wrong_expected_pin',HERE/'GroupDefs.lean','0'*64)]:
 try:require_sha(path,digest)
 except AssertionError as err:record['controls'][label]='CAUGHT: '+str(err)
 else:raise AssertionError('source corruption survived: '+label)
for rel,digest in record['input_hashes'].items():require_sha(ROOT/rel,digest)
for r in DEPS:
 s=(ROOT/r['path']).read_text()
 for old,new in r['adaptations'].items():s=s.replace('import '+old+'\n','import '+new+'\n',1)
 assert (OUT/(r['module']+'.lean')).read_text()==s
for n in LOCAL:assert (OUT/(n+'.lean')).read_bytes()==(HERE/(n+'.lean')).read_bytes()
record.update(status='PASS_AUTHOR_KERNEL_REPLAY',grouped_forward='CLOSED_UNVERIFIED',grouped_reverse='CLOSED_UNVERIFIED',exact_cost='CLOSED_UNVERIFIED',retained_A_one_Bforest='CLOSED_UNVERIFIED',conditional_residual_query='CLOSED_UNVERIFIED',first_unproved_consumer='A concrete recursive solver meeting the child-specific ResidualSolverContract; full original source-cut reconstruction remains separate.')
record['module_inventory_sha256']=sha(OUT/'ModuleInventory.log')
record['source_modules']=MODS
record['recorded_invocation_seconds']=round(sum(x['seconds'] for x in record['builds']),6)
save()
print(json.dumps({k:record[k] for k in ['status','grade','all_three_main_milestones','fresh_nonauthor_acceptance','module_origin_total','module_origin_counts','axiom_union_observed','controls','recorded_invocation_seconds','first_unproved_consumer']},indent=2))
print('receipt: '+str(OUT))
