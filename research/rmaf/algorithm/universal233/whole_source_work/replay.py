#!/usr/bin/env python3
"""One-shot isolated original-source runtime consumer; no frozen writes.
Author source-operation/kernel evidence, not independent nonauthor review.
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
SPECS += [(n,BASE/'whole_source_mass'/(n+'.lean')) for n in ['WholeColors','OriginalColors','WholeMass','MassControls']]
SPECS += [(n,BASE/'core_work'/(n+'.lean')) for n in ['Work','Primitive','Payload']]
SPECS += [(n,HERE/(n+'.lean')) for n in ['ColorWork','GeometryWork','OwnershipWork','RuntimeAssembly','WorkControls']]
NEGATIVES=['FalseColorCount','FalsePruned','FalseAppend']
ALLOWED={'propext','Quot.sound','Classical.choice'}

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def clean(s):
    s=re.sub(r'/\-.*?\-/',lambda m:'\n'*m.group().count('\n'),s,flags=re.S)
    return re.sub(r'--[^\n]*','',s)
def check_pin(p,h):
    if digest(p)!=h: raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))

stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT=ROOT/'results'/('algorithm-universal233-whole-work-'+stamp)
OUT.mkdir(parents=True,exist_ok=False)
(HERE/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
ENV=dict(os.environ,LEAN_PATH=str(OUT))
record={'status':'RUNNING','grade':'AUTHOR_SOURCE_OPERATION_AND_KERNEL_CHECK',
 'fresh_nonauthor_review':'PENDING','full_faster_algorithm_proved':False,
 'all_three_main_milestones':'OPEN','ordinary_rooted_convention':'q=k-1; no implicit rho',
 'source_correspondence':'Proof by inspection in COST-MODEL.md; kernel checks concrete meters/projections/bounds, not extracted machine instructions.',
 'frozen_manifests':{},'frozen_input_hashes':{},'input_hashes':{},'builds':[],'controls':{},
 'first_remaining_runtime_consumer':'Fresh nonauthor source-operation review; then compose the still-open actual hard-parent/refinement and pair G/E selectors, progress, history and reconstruction with these caller costs and strict macro margin. No pair selector cost is supplied here.'}
def save(): (OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def save_interrupted():
    if record['status']=='RUNNING':
        record['status']='FAIL_OR_INTERRUPTED_AUTHOR_CHECK'
        record['failure']='Final acceptance block was not reached; retained logs identify the failing module.'
        save()
atexit.register(save_interrupted)
def run(n,build=False):
    args=[str(ROOT/'bootloops-lean')]
    if build:args += ['-o',str(OUT/(n+'.olean'))]
    args += [str(OUT/(n+'.lean'))]
    start=time.monotonic()
    p=subprocess.run(args,cwd=ROOT,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
    (OUT/(n+'.log')).write_text(p.stdout)
    row={'module':n,'seconds':round(time.monotonic()-start,6),'returncode':p.returncode}
    record['builds'].append(row);save()
    print(json.dumps(row),flush=True)
    return p

# Known-answer pipeline controls precede the actual-source replay.
(OUT/'TrueControl.lean').write_text('import Std\ntheorem runtime_audit_true : (2 : Nat)+3=5 := by decide\n')
(OUT/'FalseControl.lean').write_text('import Std\ntheorem runtime_audit_false : (0 : Nat)=1 := by decide\n')
p=run('TrueControl');assert p.returncode==0,p.stdout
p=run('FalseControl');assert p.returncode!=0 and 'is false' in p.stdout,p.stdout
record['controls']['known_true']='ACCEPTED'
record['controls']['known_false']='REJECTED'
pin_fixture=OUT/'PinFixture.txt';pin_fixture.write_text('known source fixture\n')
check_pin(pin_fixture,digest(pin_fixture))
try:check_pin(pin_fixture,'0'*64)
except ValueError as e:
    assert 'SOURCE_PIN_MISMATCH|' in str(e)
    record['controls']['source_pin_plant']='CAUGHT_WITH_CLEAN_TWIN'
else:raise AssertionError('source-pin plant survived')

for mp in [BASE/'core_work/CORE-WORK-MANIFEST-v1.json',BASE/'whole_source_mass/WHOLE-SOURCE-MASS-MANIFEST-v1.json']:
    m=json.loads(mp.read_text());record['frozen_manifests'][str(mp.relative_to(ROOT))]=digest(mp)
    for item in m['immutable_files']:
        check_pin(ROOT/item['path'],item['sha256'])
        record['frozen_input_hashes'][item['path']]=item['sha256']
for n,p in SPECS:
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(p.read_text())):
        raise AssertionError('forbidden positive source escape: '+str(p))
    (OUT/(n+'.lean')).write_bytes(p.read_bytes())
    record['input_hashes'][str(p.relative_to(ROOT))]=digest(p)
for n in NEGATIVES:
    p=HERE/(n+'.lean');(OUT/p.name).write_bytes(p.read_bytes())
    record['input_hashes'][str(p.relative_to(ROOT))]=digest(p)
for p in [Path(__file__),HERE/'lean-toolchain',HERE/'COST-MODEL.md',HERE/'README.md',HERE/'RESULT.md']:
    record['input_hashes'][str(p.relative_to(ROOT))]=digest(p)
(OUT/'lean-toolchain').write_bytes((HERE/'lean-toolchain').read_bytes())
for n,_ in SPECS:
    p=run(n,True)
    assert p.returncode==0 and not re.search(r'error:|sorryAx|declaration uses .sorry.',p.stdout),(n,p.stdout)
for n in NEGATIVES:
    p=run(n)
    assert p.returncode!=0 and 'is false' in p.stdout,(n,p.stdout)
    record['controls'][n]='REJECTED'

modules=', '.join('`'+n for n,_ in SPECS)
inventory='''import WorkControls
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
    assert len({n for _,n in m})==len(m), 'duplicate declaration origin'
    assert {n for _,n in m}=={n for n,_ in a}, 'missing axiom record'
    return m,a
m,a=parse(p.stdout)
try:parse(re.sub(r'^MODAUDIT\|[^\n]*\n','',p.stdout,count=1,flags=re.M))
except AssertionError:record['controls']['missing_audit_record']='CAUGHT_WITH_CLEAN_TWIN'
else:raise AssertionError('missing-record plant survived')
record['module_origin_counts']={n:sum(mod==n for mod,_ in m) for n,_ in SPECS}
assert all(record['module_origin_counts'].values()),record['module_origin_counts']
record['module_origin_total']=len(m)
record['private_generated_origin_records']=sum(n.startswith('_private.') for _,n in m)
assert record['private_generated_origin_records']>0
record['axiom_union_observed']=sorted({v.strip() for _,xs in a for v in xs.split(',') if v.strip()})
assert set(record['axiom_union_observed'])<=ALLOWED,record['axiom_union_observed']
(OUT/'PlantModel.lean').write_text('namespace WholeWorkOutside\nprivate axiom hidden : False\ntheorem borrowed : False := hidden\nend WholeWorkOutside\n')
p=run('PlantModel',True);assert p.returncode==0,p.stdout
(OUT/'ModulePlantAudit.lean').write_text('import PlantModel\n'+inventory.replace('`WorkControls]','`WorkControls, `PlantModel]'))
p=run('ModulePlantAudit')
assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM|' in p.stdout and 'WholeWorkOutside' in p.stdout,p.stdout
record['controls']['hidden_private_custom_axiom']='CAUGHT'
for rel,h in record['input_hashes'].items():check_pin(ROOT/rel,h)
for rel,h in record['frozen_input_hashes'].items():check_pin(ROOT/rel,h)
for rel,h in record['frozen_manifests'].items():check_pin(ROOT/rel,h)
record['module_audit_sha256']=digest(OUT/'ModuleInventory.log')
record['status']='PASS_AUTHOR_SOURCE_OPERATION_KERNEL_CHECK'
record['actual_whole_source_runtime_consumer']='CLOSED_UNVERIFIED_AUTHOR_CHECKPOINT'
record['positive_source_modules']=len(SPECS)
record['positive_fixture_theorems']=14
record['positive_source_build_seconds']=sum(x['seconds'] for x in record['builds'] if x['module'] in dict(SPECS))
record['scope']='Actual tagged-color costs and exact n calls; finite original-target clique/common selection and joint gate; frozen capped generate at unchanged q; literal 3/4/2 lists, outer append copies, raw rational masses and conditional strict additive-overhead absorption.'
save()
print(json.dumps({k:record[k] for k in ['status','positive_source_modules','module_origin_total','private_generated_origin_records','axiom_union_observed','controls']},indent=2))
print('receipt='+str(OUT.relative_to(ROOT)),flush=True)
