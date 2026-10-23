#!/usr/bin/env python3
"""One-shot kept-parent source-bound author kernel audit; no independent review."""
from pathlib import Path
import atexit,datetime,hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=HERE.parent
SPECS=[('RMAF',ROOT/'research/rmaf/lean/RMAF.lean')]
SPECS += [(n,BASE/'geometry'/(n+'.lean')) for n in ['Geometry','Bridge','Composition']]
SPECS += [(n,BASE/'core'/(n+'.lean')) for n in ['CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants']]
SPECS += [(n,BASE/'integration'/(n+'.lean')) for n in ['SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','CutRecords']]
SPECS += [(n,BASE/'source_coverage'/(n+'.lean')) for n in ['FullTransport','Coverage','Entrypoint','OutputBudget','ColorBudget','ColorSteps','RawMass','RationalMass']]
SPECS += [('ParentColors',BASE/'assembly/ParentColors.lean')]
SPECS += [(('CutCoverage' if n=='Coverage' else n),BASE/'cut_realization'/(n+'.lean')) for n in ['OriginalGraph','Display','Regions','History','Realization','OwnerCover','Coverage','InitialCoverage','Cost','ValidPartition']]
LOCAL=['KeptGraph','KeptRun','KeptParent','KeptConsumers','KeptControls']
SPECS += [(n,HERE/(n+'.lean')) for n in LOCAL]
NEGATIVE=['FalseKeptGuard','FalseKeptOverlap','FalseKeptWholeTag','FalseKeptCompleteness','FalseKeptLogic']
ALLOWED={'propext','Quot.sound','Classical.choice'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check_pin(p,h):
 if digest(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def clean(s):
 s=re.sub(r'/\-.*?\-/',lambda m:'\n'*m.group().count('\n'),s,flags=re.S)
 return re.sub(r'--[^\n]*','',s)
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT=ROOT/'results'/('algorithm-universal233-kept-'+stamp);OUT.mkdir(parents=True,exist_ok=False)
(HERE/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
ENV=dict(os.environ,LEAN_PATH=str(OUT))
record={'status':'RUNNING','grade':'AUTHOR_KERNEL_CHECK; fresh nonauthor review required',
 'all_three_main_milestones':'OPEN','universal_kept_parent_kernel_checked':False,
 'full_algorithm_proved':False,'source_cut_lift_consumer_proved':False,
 'source_hashes':{},'compiled_hashes':{},'builds':[],'controls':{},'adapters':[],
 'first_remaining_graph_call':'Lift the supplied local restricted-A source-cut address to a compatible original S cut address after every literal whole-source output; establish union realization, nonredundancy and paid combined charge. Membership and unchanged local restrictions alone do not establish this lift.'}
def save():(OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def interrupted():
 if record['status']=='RUNNING':
  record['status']='FAIL_OR_INTERRUPTED';save()
atexit.register(interrupted)
def run(n,build=False):
 args=[str(ROOT/'bootloops-lean')]
 if build:args+=['-o',str(OUT/(n+'.olean'))]
 args+=[str(OUT/(n+'.lean'))]
 start=time.monotonic();r=subprocess.run(args,cwd=ROOT,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (OUT/(n+'.log')).write_text(r.stdout)
 record['builds'].append({'module':n,'seconds':time.monotonic()-start,'returncode':r.returncode});save();return r

# Known controls before this source/proof replay. The finite development and
# actual literal controls were separately frozen and run before proof authoring.
(OUT/'TrueControl.lean').write_text('import Std\ntheorem kept_true : (2 : Nat)+3=5 := by decide\n')
r=run('TrueControl');assert r.returncode==0,r.stdout
(OUT/'FalseControl.lean').write_text('import Std\ntheorem kept_false : (0 : Nat)=1 := by decide\n')
r=run('FalseControl');assert r.returncode!=0 and 'is false' in r.stdout,r.stdout
record['controls']['known_true']='ACCEPTED';record['controls']['known_false']='REJECTED'
pin=OUT/'PinFixture.txt';pin.write_text('exact source fixture\n');check_pin(pin,digest(pin))
try:check_pin(pin,'0'*64)
except ValueError as e:
 assert 'SOURCE_PIN_MISMATCH' in str(e);record['controls']['source_pin_plant']='CAUGHT_WITH_CLEAN_TWIN'
else:raise AssertionError('source pin plant survived')

frozen={};record['frozen_manifests']={}
for p in [BASE/'source_coverage/SOURCE-COVERAGE-MANIFEST-v1.json',BASE/'cut_realization/CUT-REALIZATION-MANIFEST-v1.json',BASE/'assembly/ASSEMBLY-MANIFEST-v1.json']:
 m=json.loads(p.read_text());record['frozen_manifests'][str(p.relative_to(ROOT))]=digest(p)
 for row in m.get('immutable_files',[]):frozen[row['path']]=row['sha256']
 frozen.update(m.get('owned_files',{}));frozen.update(m.get('exact_source_import_pins',{}))
ownpath=HERE/'KEPT-PARENT-MANIFEST-v1.json';own=json.loads(ownpath.read_text())
record['own_manifest_sha256']=digest(ownpath)
for rel,h in own['source_pins'].items():check_pin(ROOT/rel,h)
for n,p in SPECS:
 rel=str(p.relative_to(ROOT))
 expected=own['source_pins'].get(rel) if n in LOCAL else frozen.get(rel)
 assert expected,'MISSING_FROZEN_SOURCE_PIN|'+rel
 check_pin(p,expected)
 data=p.read_bytes()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(data.decode())),str(p)
 if n=='InitialCoverage':
  assert data.startswith(b'import Coverage\n')
  data=data.replace(b'import Coverage\n',b'import CutCoverage\n',1)
  record['adapters'].append({'module':n,'change':'single import module path Coverage -> CutCoverage; proof body unchanged'})
 if n=='CutCoverage':record['adapters'].append({'module':n,'change':'module filename only Coverage -> CutCoverage'})
 (OUT/(n+'.lean')).write_bytes(data)
 record['source_hashes'][rel]=digest(p);record['compiled_hashes'][n]=hashlib.sha256(data).hexdigest()
for n in NEGATIVE:
 p=HERE/(n+'.lean');(OUT/p.name).write_bytes(p.read_bytes());record['source_hashes'][str(p.relative_to(ROOT))]=digest(p)
for n,_ in SPECS:
 r=run(n,True)
 assert r.returncode==0 and not re.search(r'error:|sorryAx|declaration uses .sorry.',r.stdout),(n,r.stdout)
for n in NEGATIVE:
 r=run(n);assert r.returncode!=0 and 'is false' in r.stdout,(n,r.stdout)
 record['controls'][n]='REJECTED'

modules=', '.join('`'+n for n,_ in SPECS)
inventory='''import KeptControls
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [MODULES]
  let ns := (env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)
  let ns := (ns.filter fun n =>
    match env.getModuleIdxFor? n with
    | some idx => modules.contains env.header.moduleNames[idx.toNat]!
    | none => false).eraseDups
  for n in ns do
    let some idx := env.getModuleIdxFor? n | throwError "missing origin module"
    let mod := env.header.moduleNames[idx.toNat]!
    logInfo m!"MODULE|{mod}|{n}"
  for n in ns do
    let axs ← collectAxioms n
    logInfo m!"MODAUDIT|{n}|{String.intercalate "," (axs.toList.map toString)}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
'''.replace('MODULES',modules)
(OUT/'ModuleInventory.lean').write_text(inventory)
r=run('ModuleInventory');assert r.returncode==0,r.stdout

def parse(s):
 m=re.findall(r'^MODULE\|([^|]+)\|(.+)$',s,re.M);a=re.findall(r'^MODAUDIT\|([^|]+)\|([^\n]*)$',s,re.M)
 assert m and len(m)==len(a) and len(m)==len(set(m)),'missing/duplicate origin record'
 assert {n for _,n in m}=={n for n,_ in a},'missing axiom record'
 return m,a
m,a=parse(r.stdout)
try:parse(re.sub(r'^MODAUDIT\|[^\n]*\n','',r.stdout,count=1,flags=re.M))
except AssertionError:record['controls']['missing_audit_record']='CAUGHT_WITH_CLEAN_TWIN'
else:raise AssertionError('missing audit record plant survived')
record['module_origin_counts']={n:sum(mod==n for mod,_ in m) for n,_ in SPECS}
assert all(record['module_origin_counts'].values()),record['module_origin_counts']
record['module_origin_total']=len(m)
record['axiom_union_observed']=sorted({v.strip() for _,xs in a for v in xs.split(',') if v.strip()})
assert set(record['axiom_union_observed'])<=ALLOWED
(OUT/'PlantModel.lean').write_text('namespace KeptForeign\nprivate axiom hidden : False\ntheorem borrowed : False := hidden\nend KeptForeign\n')
r=run('PlantModel',True);assert r.returncode==0,r.stdout
(OUT/'ModulePlantAudit.lean').write_text('import PlantModel\n'+inventory.replace('`KeptControls]','`KeptControls, `PlantModel]'))
r=run('ModulePlantAudit');assert r.returncode!=0 and 'REJECT_CUSTOM_AXIOM|' in r.stdout and 'KeptForeign' in r.stdout,r.stdout
record['controls']['private_foreign_custom_axiom']='CAUGHT'
for rel,h in own['source_pins'].items():check_pin(ROOT/rel,h)
for rel,h in record['source_hashes'].items():check_pin(ROOT/rel,h)
record['positive_source_modules']=len(SPECS)
record['positive_build_seconds']=sum(b['seconds'] for b in record['builds'] if b['module'] in dict(SPECS))
record['module_inventory_sha256']=digest(OUT/'ModuleInventory.log')
record['status']='PASS_AUTHOR_KERNEL_CHECK'
record['universal_kept_parent_kernel_checked']=True
save()
print(json.dumps({k:record[k] for k in ['status','positive_source_modules','module_origin_total','axiom_union_observed','controls','first_remaining_graph_call']},indent=2))
print('receipt='+str(OUT.relative_to(ROOT)))
