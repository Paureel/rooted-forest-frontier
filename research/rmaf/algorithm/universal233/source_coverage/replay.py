#!/usr/bin/env python3
"""One-shot source-bound proof replay and complete module-origin audit.
Uses exact frozen source imports, preserves failed controls and development logs.
Author checking is not independent nonauthor verification or algorithm closure.
"""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = HERE.parent
SPECS = [('RMAF', ROOT/'research/rmaf/lean/RMAF.lean')]
SPECS += [(n, BASE/'geometry'/(n+'.lean')) for n in ['Geometry','Bridge','Composition']]
SPECS += [(n, BASE/'core'/(n+'.lean')) for n in ['CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants']]
SPECS += [(n, BASE/'integration'/(n+'.lean')) for n in ['SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','CutRecords']]
SPECS += [(n, HERE/(n+'.lean')) for n in ['FullTransport','Coverage','Entrypoint','OutputBudget','ColorBudget','ColorSteps','RawMass','RationalMass','Controls']]
NEGATIVES = ['FalseBudgetZero','FalseExactPartition','FalseDuplicateMass']
ALLOWED = {'propext','Quot.sound','Classical.choice'}

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def clean(s):
    s = re.sub(r'/\-.*?\-/', lambda m: '\n'*m.group().count('\n'), s, flags=re.S)
    return re.sub(r'--[^\n]*','',s)

stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT = HERE/'replay'/stamp
OUT.mkdir(parents=True,exist_ok=False)
(HERE/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
ENV = dict(os.environ,LEAN_PATH=str(OUT))
record = {'status':'RUNNING','grade':'AUTHOR DEVELOPMENT KERNEL REPLAY; nonauthor review pending',
          'production_algorithm_proved':False,'original_cut_realization_proved':False,
          'source_partition_coverage_proved':False,'recorded_color_cost_proved':False,
          'raw_rational_mass_proved':False,'polynomial_per_prefix_proved':False,
          'builds':[],'controls':{},'input_hashes':{}}
manifest = json.loads((BASE/'INTEGRATION-MANIFEST-v1.json').read_text())
for item in manifest['immutable_files']:
    p=ROOT/item['path']
    if digest(p)!=item['sha256']: raise RuntimeError('frozen input changed: '+str(p))
record['frozen_manifest_sha256']=digest(BASE/'INTEGRATION-MANIFEST-v1.json')
for _,p in SPECS:
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(p.read_text())):
        raise RuntimeError('forbidden proof escape: '+str(p))
    (OUT/p.name).write_bytes(p.read_bytes())
    record['input_hashes'][str(p.relative_to(ROOT))]=digest(p)
for n in NEGATIVES:
    p=HERE/(n+'.lean');(OUT/p.name).write_bytes(p.read_bytes())
    record['input_hashes'][str(p.relative_to(ROOT))]=digest(p)
(OUT/'lean-toolchain').write_bytes((BASE/'integration/lean-toolchain').read_bytes())
record['input_hashes'][str(Path(__file__).relative_to(ROOT))]=digest(Path(__file__))

def save(): (OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def run(n,build=False):
    args=[str(ROOT/'bootloops-lean')]
    if build:args+=['-o',str(OUT/(n+'.olean'))]
    args+=[str(OUT/(n+'.lean'))]
    start=time.monotonic()
    p=subprocess.run(args,cwd=ROOT,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
    (OUT/(n+'.log')).write_text(p.stdout)
    record['builds'].append({'module':n,'returncode':p.returncode,'seconds':round(time.monotonic()-start,6)})
    save();return p

# Plants precede the real proof replay.
(OUT/'TrueControl.lean').write_text('import Std\ntheorem true_control : (2 : Nat) + 3 = 5 := by decide\n')
(OUT/'FalseControl.lean').write_text('import Std\ntheorem false_control : (0 : Nat) = 1 := by decide\n')
p=run('TrueControl');assert p.returncode==0,p.stdout
p=run('FalseControl');assert p.returncode!=0 and 'is false' in p.stdout,p.stdout
record['controls']['known_true']='ACCEPTED'
record['controls']['known_false']='REJECTED'
for n,_ in SPECS:
    p=run(n,True)
    assert p.returncode==0 and not re.search(r'error:|sorryAx|declaration uses .sorry.',p.stdout),(n,p.stdout)
for n in NEGATIVES:
    p=run(n)
    assert p.returncode!=0 and 'is false' in p.stdout,(n,p.stdout)
    record['controls'][n]='REJECTED'

modules=', '.join('`'+n for n,_ in SPECS)
inventory='''import Controls
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
    let some idx := env.getModuleIdxFor? n | throwError "missing module"
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
    assert {n for _,n in m}=={n for n,_ in a},'missing axiom record'
    return m,a
m,a=parse(p.stdout)
try:parse(re.sub(r'^MODAUDIT\|[^\n]+\n','',p.stdout,count=1,flags=re.M))
except AssertionError:record['controls']['missing_audit_record']='CAUGHT'
else:raise AssertionError('missing record corruption survived')
record['module_origin_counts']={n:sum(mod==n for mod,_ in m) for n,_ in SPECS}
record['module_origin_total']=len(m)
record['axiom_union_observed']=sorted({v.strip() for _,xs in a for v in xs.split(',') if v.strip()})
assert set(record['axiom_union_observed'])<=ALLOWED,record['axiom_union_observed']
# Deliberate isolated custom-axiom model; never imported into the positive chain.
(OUT/'PlantModel.lean').write_text('namespace OutsideCoverage\naxiom borrowed : False\nend OutsideCoverage\n')
p=run('PlantModel',True);assert p.returncode==0,p.stdout
(OUT/'ModulePlantAudit.lean').write_text('import PlantModel\n'+inventory.replace('`Controls]','`Controls, `PlantModel]'))
p=run('ModulePlantAudit')
assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM|OutsideCoverage.borrowed|OutsideCoverage.borrowed' in p.stdout,p.stdout
record['controls']['hidden_custom_axiom']='CAUGHT'
for rel,h in record['input_hashes'].items():
    assert digest(ROOT/rel)==h,'source changed during replay: '+rel
for item in manifest['immutable_files']:
    assert digest(ROOT/item['path'])==item['sha256'],'frozen source changed during replay'
record['status']='PASS_AUTHOR_KERNEL_CHECK'
record['source_partition_coverage_proved']=True
record['recorded_color_cost_proved']=True
record['raw_rational_mass_proved']=True
record['first_remaining_consumer']='Original cut-component realization at actual attempt; polynomial per-prefix work and complete faster algorithm integration remain separate.'
record['module_audit_sha256']=digest(OUT/'ModuleInventory.log')
save()
summary={k:record[k] for k in ['status','source_partition_coverage_proved','production_algorithm_proved','module_origin_total','axiom_union_observed','controls']}
print(json.dumps(summary,indent=2))
print('receipt='+str(OUT.relative_to(ROOT)))
