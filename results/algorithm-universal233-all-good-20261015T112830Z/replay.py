#!/usr/bin/env python3
"""One-shot all-good case replay, wrapping completed source-bound audit practice.

All result writes are fresh. No frozen source, upstream proof, pin, or receipt
is changed. This is a project-specific proof/evidence instrument.
"""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, time

D=Path(__file__).resolve().parent
ROOT=D.parents[4]
STAMP=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT=ROOT/'results'/('algorithm-universal233-all-good-'+STAMP)
OUT.mkdir(exist_ok=False)
ENV=dict(os.environ,LEAN_PATH=str(OUT))
ALLOWED={'propext','Quot.sound','Classical.choice'}
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
    if digest(p)!=h: raise AssertionError('SOURCE_PIN_MISMATCH: '+str(p))
def clean(s):
    s=re.sub(r'/\-.*?\-/',lambda m:'\n'*m.group().count('\n'),s,flags=re.S)
    return re.sub(r'--[^\n]*','',s)
pins=json.loads((D/'DEPENDENCY-PINS-v1.json').read_text())
for p,h in pins['pins'].items(): pin(ROOT/p,h)
FM=ROOT/'research/rmaf/algorithm/universal233/final_cut_recovery/FINAL-CUTS-MANIFEST-v1.json'
fm=json.loads(FM.read_text())
frozen={x['path']:x['sha256'] for x in fm['immutable_files']}
FR=ROOT/Path(fm['canonical_receipt']).parent
pin(FR/'certificate.json',frozen[str((FR/'certificate.json').relative_to(ROOT))])
final=json.loads((FR/'certificate.json').read_text())
RM=ROOT/'research/rmaf/algorithm/universal233/restriction_bridge/RESTRICTION-MANIFEST-v1.json'
SM=ROOT/'research/rmaf/algorithm/universal233/state_reductions/STATE-MANIFEST-v1.json'
frozen.update({x['path']:x['sha256'] for x in json.loads(RM.read_text())['immutable_files']})
frozen.update({x['path']:x['sha256'] for x in json.loads(SM.read_text())['immutable_files']})
sources=[]
order=[]
record={'status':'RUNNING_AUTHOR_SOURCE_BOUND_REPLAY','all_good_exact_case':'PENDING',
 'all_three_main_milestones':'OPEN','fresh_nonauthor_acceptance':False,'novelty':'NO_CLAIM',
 'source_inputs':sources,'positive_order':order,'runs':[],'controls':{},
 'input_hashes':{},'dependency_manifest_pins':pins,
 'final_cut_receipt':str((FR/'certificate.json').relative_to(ROOT)),
 'final_cut_receipt_sha256':digest(FR/'certificate.json'),
 'source_cost_qualification':'COST-MODEL.md source-operation audit; kernel row/visit algebra is separate from helper-to-primitive correspondence and compiled-machine semantics',
 'timing':{'basis':'Same-host pre-proof six-module pilot 7.94 seconds, including original RMAF 5.53 seconds; each new proof module measured below one second; completed final-cut replay source pass is reused in type, not trusted without rebuilding',
 'plan':'One isolated finite source pass; each compiler invocation capped at 60 seconds; no mathematical search or toolkit-wide suite retry'},
 'preproof_receipt':json.loads((D/'dev/preproof/receipt.json').read_text())}
def save(): (OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def add(name,path,adapt=None,pinned=True):
    rel=str(path.relative_to(ROOT))
    if pinned:
        if rel in frozen: pin(path,frozen[rel])
        else:
            row=next(x for x in final['source_inputs'] if x['compiled_module']==name)
            pin(path,row['compiled_sha256'])
    s=path.read_text()
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(s)):
        raise AssertionError('PROOF_ESCAPE: '+rel)
    if adapt:
        old,new=adapt
        assert s.count(old)==1,(name,old)
        s=s.replace(old,new,1)
    (OUT/(name+'.lean')).write_text(s)
    sources.append({'module':name,'source':rel,'source_sha256':digest(path),
        'adaptation':adapt,'snapshot_sha256':digest(OUT/(name+'.lean'))})
    order.append(name)
for name in final['positive_order']:
    add(name,FR/(name+'.lean'))
assert (OUT/'RMAF.lean').read_bytes()==(ROOT/'research/rmaf/lean/RMAF.lean').read_bytes()
for new,old,adapt in [
    ('StateRestriction','Restriction',None),
    ('StateEmbedding','Embedding',('import Restriction','import StateRestriction')),
    ('StatePartition','Partition',('import Embedding','import StateEmbedding')),
    ('StateCost','Cost',('import Partition','import StatePartition'))]:
    add(new,D.parent/'restriction_bridge'/(old+'.lean'),adapt)
add('State',D.parent/'state_reductions/State.lean')
LOCAL=['PreControls','ColorDP','ColorRegions','ActualProgram','TargetEmbedding','IsoTransport',
       'StateSoundness','CutColoring','LowerBound','ExactMinimum','DPControls','ConsumerControls']
for name in LOCAL: add(name,D/(name+'.lean'),pinned=False)
for path in [D/'TARGET-v1.md',D/'CONTROLS-PIN-v1.json',D/'CONTROLS-v1.md',D/'DEPENDENCY-PINS-v1.json',
             D/'COST-MODEL.md',D/'INTERFACE.md',D/'README.md',D/'RESULT.md',D/'precontrols.py',
             D/'FalseControls.lean',D/'DPFalseControls.lean',Path(__file__),ROOT/'bootloops-lean',
             ROOT/'bootloops-python']:
    record['input_hashes'][str(path.relative_to(ROOT))]=digest(path)
    if path.parent==D: (OUT/path.name).write_bytes(path.read_bytes())
(OUT/'preproof-receipt.json').write_bytes((D/'dev/preproof/receipt.json').read_bytes())
(OUT/'lean-toolchain').write_bytes((ROOT/'research/rmaf/lean/lean-toolchain').read_bytes())
def run(name,build=False):
    begin=time.monotonic()
    args=[str(ROOT/'bootloops-lean')]+(['-o',str(OUT/(name+'.olean'))] if build else [])+[str(OUT/(name+'.lean'))]
    p=subprocess.run(args,cwd=ROOT,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
    (OUT/(name+'.log')).write_text(p.stdout)
    record['runs'].append({'module':name,'exit':p.returncode,'seconds':round(time.monotonic()-begin,6)})
    save()
    return p
(OUT/'KnownTrue.lean').write_text('import Std\nexample : (2 : Nat)+3=5 := by decide\n')
(OUT/'KnownFalse.lean').write_text('import Std\nexample : (2 : Nat)+3=6 := by decide\n')
assert run('KnownTrue').returncode==0
p=run('KnownFalse');assert p.returncode!=0 and 'is false' in p.stdout,p.stdout
record['controls'].update(known_true='ACCEPTED',known_false='REJECTED')
for name in order:
    p=run(name,True)
    assert p.returncode==0 and not re.search(r'error:|sorryAx|declaration uses .sorry.',p.stdout),(name,p.stdout)
for name in ['FalseControls','DPFalseControls']:
    p=run(name)
    assert p.returncode!=0 and p.stdout.count('is false')==4,(name,p.stdout)
    record['controls'][name]='REJECTED_4_OF_4'

def inventory(modules,plant=False):
    return '\n'.join('import '+m for m in order+(['PlantModel'] if plant else []))+'''
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
'''.replace('MODULES',', '.join('`'+m for m in modules))
def parse(s,mods):
    origins=re.findall(r'^MODULE\|([^|]+)\|(.+)$',s,re.M)
    axioms=re.findall(r'^MODAUDIT\|([^|]+)\|([^\n]*)$',s,re.M)
    assert origins and len(origins)==len(axioms)==len(set(origins)),'incomplete/duplicate audit'
    assert {n for _,n in origins}=={n for n,_ in axioms},'missing axiom record'
    assert {m for m,_ in origins}==set(mods),'missing/extra source origin'
    paths=dict(re.findall(r'^PATH\|([^|]+)\|(.+)$',s,re.M))
    for mod,raw in paths.items():
        p=Path(raw).resolve()
        if mod in mods: assert p==OUT/(mod+'.olean'),'wrong local module path: '+mod
        else: assert p.is_relative_to(ROOT/'.runtime/elan/toolchains'),'foreign module path: '+mod
    for mod in mods: assert mod in paths,'missing module path: '+mod
    observed={a.strip() for _,aa in axioms for a in aa.split(',') if a.strip()}
    assert observed<=ALLOWED,'nonstandard axiom: '+str(observed-ALLOWED)
    return origins,axioms,paths,observed
(OUT/'ModuleInventory.lean').write_text(inventory(order))
p=run('ModuleInventory');assert p.returncode==0,p.stdout
origins,axioms,paths,observed=parse(p.stdout,order)
for label,bad in [
    ('missing_axiom_record',re.sub(r'^MODAUDIT\|[^\n]*\n','',p.stdout,count=1,flags=re.M)),
    ('wrong_module_origin',re.sub(r'^MODULE\|ColorDP\|','MODULE|ForeignModule|',p.stdout,count=1,flags=re.M)),
    ('wrong_module_path',re.sub(r'^PATH\|ColorDP\|[^\n]+','PATH|ColorDP|/tmp/foreign.olean',p.stdout,flags=re.M))]:
    try: parse(bad,order)
    except AssertionError as err: record['controls'][label]='CAUGHT: '+str(err)
    else: raise AssertionError('CORRUPTION_SURVIVED: '+label)
(OUT/'PlantModel.lean').write_text('namespace HiddenAllGoodPlant\naxiom borrowed : False\nend HiddenAllGoodPlant\n')
assert run('PlantModel',True).returncode==0
(OUT/'PlantAudit.lean').write_text(inventory(order+['PlantModel'],True))
p=run('PlantAudit')
assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM|HiddenAllGoodPlant.borrowed|HiddenAllGoodPlant.borrowed' in p.stdout,p.stdout
record['controls']['hidden_custom_axiom']='CAUGHT'
bad=OUT/'ColorDP-corrupted.txt'
bad.write_bytes((OUT/'ColorDP.lean').read_bytes()+b'\n-- deliberate corruption\n')
try: pin(bad,digest(D/'ColorDP.lean'))
except AssertionError as err: record['controls']['source_byte_corruption']='CAUGHT: '+str(err)
else: raise AssertionError('SOURCE_CORRUPTION_SURVIVED')
for row in sources:
    pin(ROOT/row['source'],row['source_sha256'])
    pin(OUT/(row['module']+'.lean'),row['snapshot_sha256'])
for rel,h in record['input_hashes'].items(): pin(ROOT/rel,h)
for rel,h in pins['pins'].items(): pin(ROOT/rel,h)
record.update(status='PASS_AUTHOR_KERNEL_CLOSED_UNVERIFIED_ALL_GOOD',all_good_exact_case='CLOSED_UNVERIFIED',
    module_origin_total=len(origins),module_origin_counts={m:sum(mm==m for mm,_ in origins) for m in order},
    axiom_union_observed=sorted(observed),resolved_module_paths=paths,
    audit_sha256=digest(OUT/'ModuleInventory.log'),first_unproved_subcase_theorem=None,
    acceptance_remaining='Fresh nonauthor semantic/interface/source-cost and fresh-context prose/referee review',
    compilation_seconds=sum(x['seconds'] for x in record['runs']))
save()
print(json.dumps({k:record[k] for k in ['status','all_good_exact_case','all_three_main_milestones',
    'module_origin_total','axiom_union_observed','controls','compilation_seconds','acceptance_remaining']}
    | {'receipt':str(OUT.relative_to(ROOT))},indent=2))
