#!/usr/bin/env python3
"""One-shot source-bound mass proof replay; author check, not independent review.

The toolkit has no rooted-MAF formal color-cardinality checker. This local
instrument wraps the frozen Lean proof chain and audits module provenance.
"""
from pathlib import Path
import atexit, datetime, hashlib, json, os, re, subprocess, time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BASE=HERE.parent
SPECS=[('RMAF',ROOT/'research/rmaf/lean/RMAF.lean')]
SPECS += [(n,BASE/'geometry'/(n+'.lean')) for n in ['Geometry','Bridge','Composition']]
SPECS += [(n,BASE/'core'/(n+'.lean')) for n in ['CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants']]
SPECS += [(n,BASE/'integration'/(n+'.lean')) for n in ['SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','CutRecords']]
SPECS += [(n,BASE/'source_coverage'/(n+'.lean')) for n in ['FullTransport','Coverage','Entrypoint','OutputBudget','ColorBudget','ColorSteps','RawMass','RationalMass']]
SPECS += [(n,HERE/(n+'.lean')) for n in ['WholeColors','OriginalColors','WholeMass','MassControls']]
NEGATIVES=['FalseEmptyParent','FalseRootLabel','FalseOutputDedup','FalseChainGate']
ALLOWED={'propext','Quot.sound','Classical.choice'}

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def clean(s):
    s=re.sub(r'/\-.*?\-/',lambda m:'\n'*m.group().count('\n'),s,flags=re.S)
    return re.sub(r'--[^\n]*','',s)
def check_pin(p,h):
    if digest(p)!=h: raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))

stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT=ROOT/'results'/('algorithm-universal233-whole-mass-'+stamp)
OUT.mkdir(parents=True,exist_ok=False)
(HERE/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
ENV=dict(os.environ,LEAN_PATH=str(OUT))
record={'status':'RUNNING','grade':'AUTHOR_KERNEL_CHECK; fresh nonauthor review pending',
        'whole_source_mass_proved':False,'full_faster_algorithm_proved':False,
        'ordinary_rooted_convention':'q=k-1; no implicit rho',
        'frozen_inputs':{},'input_hashes':{},'builds':[],'controls':{},
        'first_remaining_consumer':'Compose actual original partition/refinement coverage, clearing and original-cut realization with these literal generator calls; then derive source partition/refinement from actual hard-call history. Pair-case selector/exchange and polynomial work remain separate.'}
def save(): (OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def save_interrupted():
    if record['status']=='RUNNING':
        record['status']='FAIL_OR_INTERRUPTED_AUTHOR_CHECK'
        record['failure']='Replay did not reach its final acceptance block; inspect retained module logs and invocation output.'
        save()
atexit.register(save_interrupted)
def run(n,build=False):
    args=[str(ROOT/'bootloops-lean')]
    if build:args += ['-o',str(OUT/(n+'.olean'))]
    args += [str(OUT/(n+'.lean'))]
    start=time.monotonic()
    p=subprocess.run(args,cwd=ROOT,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
    (OUT/(n+'.log')).write_text(p.stdout)
    record['builds'].append({'module':n,'seconds':round(time.monotonic()-start,6),'returncode':p.returncode})
    save()
    return p

# Frozen fixture truth and corruption tests precede the replay proper.
(OUT/'TrueControl.lean').write_text('import Std\ntheorem mass_audit_true : (2 : Nat)+3=5 := by decide\n')
(OUT/'FalseControl.lean').write_text('import Std\ntheorem mass_audit_false : (0 : Nat)=1 := by decide\n')
p=run('TrueControl');assert p.returncode==0,p.stdout
p=run('FalseControl');assert p.returncode!=0 and 'is false' in p.stdout,p.stdout
record['controls']['known_true']='ACCEPTED'
record['controls']['known_false']='REJECTED'
pin_fixture=OUT/'PinFixture.txt';pin_fixture.write_text('known exact source\n')
check_pin(pin_fixture,digest(pin_fixture))
try:check_pin(pin_fixture,'0'*64)
except ValueError as e:
    assert 'SOURCE_PIN_MISMATCH' in str(e)
    record['controls']['source_pin_plant']='CAUGHT_WITH_CLEAN_TWIN'
else:raise AssertionError('source pin plant survived')

manifest_path=BASE/'source_coverage/SOURCE-COVERAGE-MANIFEST-v1.json'
manifest=json.loads(manifest_path.read_text())
record['frozen_manifest_sha256']=digest(manifest_path)
for item in manifest['immutable_files']:
    check_pin(ROOT/item['path'],item['sha256'])
    record['frozen_inputs'][item['path']]=item['sha256']
ownmanifest=HERE/'WHOLE-SOURCE-MASS-MANIFEST-v1.json'
if ownmanifest.exists():
    own=json.loads(ownmanifest.read_text())
    for item in own['immutable_files']:check_pin(ROOT/item['path'],item['sha256'])
    record['own_frozen_manifest_sha256']=digest(ownmanifest)
for n,p in SPECS:
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(p.read_text())):
        raise AssertionError('forbidden proof escape: '+str(p))
    (OUT/(n+'.lean')).write_bytes(p.read_bytes())
    record['input_hashes'][str(p.relative_to(ROOT))]=digest(p)
for n in NEGATIVES:
    p=HERE/(n+'.lean');(OUT/p.name).write_bytes(p.read_bytes())
    record['input_hashes'][str(p.relative_to(ROOT))]=digest(p)
(OUT/'lean-toolchain').write_bytes((BASE/'integration/lean-toolchain').read_bytes())
record['input_hashes'][str(Path(__file__).relative_to(ROOT))]=digest(Path(__file__))
for n,_ in SPECS:
    p=run(n,True)
    assert p.returncode==0 and not re.search(r'error:|sorryAx|declaration uses .sorry.',p.stdout),(n,p.stdout)
for n in NEGATIVES:
    p=run(n)
    assert p.returncode!=0 and 'is false' in p.stdout,(n,p.stdout)
    record['controls'][n]='REJECTED'

modules=', '.join('`'+n for n,_ in SPECS)
inventory='''import MassControls
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
p=run('ModuleInventory');assert p.returncode==0,p.stdout
def parse(s):
    m=re.findall(r'^MODULE\|([^|]+)\|(.+)$',s,re.M)
    a=re.findall(r'^MODAUDIT\|([^|]+)\|([^\n]*)$',s,re.M)
    assert m and len(m)==len(a) and len(m)==len(set(m)), 'missing/duplicate origin record'
    assert {n for _,n in m}=={n for n,_ in a}, 'missing axiom record'
    return m,a
m,a=parse(p.stdout)
try:parse(re.sub(r'^MODAUDIT\|[^\n]*\n','',p.stdout,count=1,flags=re.M))
except AssertionError:record['controls']['missing_audit_record']='CAUGHT_WITH_CLEAN_TWIN'
else:raise AssertionError('missing audit record plant survived')
record['module_origin_counts']={n:sum(mod==n for mod,_ in m) for n,_ in SPECS}
assert all(record['module_origin_counts'].values()),record['module_origin_counts']
record['module_origin_total']=len(m)
record['axiom_union_observed']=sorted({v.strip() for _,xs in a for v in xs.split(',') if v.strip()})
assert set(record['axiom_union_observed'])<=ALLOWED,record['axiom_union_observed']
# Private hidden custom axiom and its generated use are confined to a false plant.
(OUT/'PlantModel.lean').write_text('namespace MassOutside\nprivate axiom hidden : False\ntheorem borrowed : False := hidden\nend MassOutside\n')
p=run('PlantModel',True);assert p.returncode==0,p.stdout
(OUT/'ModulePlantAudit.lean').write_text('import PlantModel\n'+inventory.replace('`MassControls]','`MassControls, `PlantModel]'))
p=run('ModulePlantAudit')
assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM|' in p.stdout and 'MassOutside' in p.stdout,p.stdout
record['controls']['hidden_private_custom_axiom']='CAUGHT'
for rel,h in record['input_hashes'].items():check_pin(ROOT/rel,h)
for rel,h in record['frozen_inputs'].items():check_pin(ROOT/rel,h)
record['module_audit_sha256']=digest(OUT/'ModuleInventory.log')
record['status']='PASS_AUTHOR_KERNEL_CHECK'
record['whole_source_mass_proved']=True
record['positive_source_modules']=len(SPECS)
record['positive_source_build_seconds']=sum(x['seconds'] for x in record['builds'] if x['module'] in dict(SPECS))
save()
print(json.dumps({k:record[k] for k in ['status','positive_source_modules','module_origin_total','axiom_union_observed','controls','first_remaining_consumer']},indent=2))
print('receipt='+str(OUT.relative_to(ROOT)))
