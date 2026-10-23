#!/usr/bin/env python3
"""One-shot completion replay extending the frozen state author replay.

Rebuild all original dependencies and new proof modules from pinned source;
isolate every local module; inventory every declaration's origin and axioms.
This author check does not replace a fresh nonauthor mathematical review.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BASE=HERE.parent/'state_reductions'
FROZEN=ROOT/'results/algorithm-universal233-state-20261015T094847Z'
STAMP=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT=ROOT/'results'/('algorithm-universal233-state-cherry-'+STAMP)
OUT.mkdir(exist_ok=False)
(HERE/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
OLD=['RMAF','StateRestriction','StateEmbedding','StatePartition','State',
     'Singleton','Removal','Forward','LeafClear','Reverse','CherryGraph','CherryTopology']
NEW=['GraphControls','Endpoint','Replacement','Contraction','BlockPartition',
     'QuotientGeometry','QuotientTopology','StateContract','Expansion','StateExpand','CompletionConsumers']
MODS=OLD+NEW
SOURCES={n:FROZEN/(n+'.lean') for n in OLD}
SOURCES.update({n:HERE/(n+'.lean') for n in NEW})
ALLOWED={'propext','Quot.sound','Classical.choice'}
ENV=dict(os.environ,LEAN_PATH=str(OUT))
record={'status':'RUNNING','grade':'AUTHOR_KERNEL_REPLAY_ONLY',
        'all_three_main_milestones':'OPEN','fresh_nonauthor_acceptance':False,
        'full_algorithm_proved':False,'builds':[],'controls':{},'input_hashes':{}}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(): (OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def clean(s):
    s=re.sub(r'/\-.*?\-/',lambda m:'\n'*m.group().count('\n'),s,flags=re.S)
    return re.sub(r'--[^\n]*','',s)
def run(n,build=False):
    args=[str(ROOT/'bootloops-lean')]
    if build: args+=['-o',str(OUT/(n+'.olean'))]
    start=time.monotonic()
    p=subprocess.run(args+[str(OUT/(n+'.lean'))],cwd=OUT,env=ENV,text=True,
        stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
    (OUT/(n+'.log')).write_text(p.stdout)
    record['builds'].append({'module':n,'returncode':p.returncode,'seconds':round(time.monotonic()-start,6)})
    save()
    return p

manifest=BASE/'STATE-MANIFEST-v1.json'
mf=json.loads(manifest.read_text())
assert len(mf['immutable_files'])==77
frozen_hashes={x['path']:x['sha256'] for x in mf['immutable_files']}
for rel,h in frozen_hashes.items(): assert sha(ROOT/rel)==h,'completed freeze changed: '+rel
record['frozen_state_manifest_sha256']=sha(manifest)
record['frozen_state_files_checked']=77
for n,p in SOURCES.items():
    rel=str(p.relative_to(ROOT))
    if n in OLD: assert sha(p)==frozen_hashes[rel]
    src=p.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(src)),str(p)
    record['input_hashes'][rel]=sha(p)
    (OUT/(n+'.lean')).write_text(src)
for p in [HERE/'TARGET-v1.md',HERE/'CONTROLS-v1.md',HERE/'CONTROLS-PIN-v1.json',
          HERE/'GraphFalseControls.lean',HERE/'preproof.py',Path(__file__),
          ROOT/'bootloops-lean',ROOT/'bootloops-lake',ROOT/'bootloops-python']:
    record['input_hashes'][str(p.relative_to(ROOT))]=sha(p)
for name in ['TARGET-v1.md','CONTROLS-v1.md','CONTROLS-PIN-v1.json','GraphFalseControls.lean']:
    (OUT/name).write_bytes((HERE/name).read_bytes())
(OUT/'preproof-controls-receipt.json').write_bytes((HERE/'preproof/receipt.json').read_bytes())
pre=json.loads((HERE/'preproof/receipt.json').read_text())
assert pre['status']=='PASS_PREPROOF_CONTROLS'
assert pre['pin_sha256']==sha(HERE/'CONTROLS-PIN-v1.json')
record['preproof_receipt_sha256']=sha(OUT/'preproof-controls-receipt.json')
for n in ['bootloops-lean','bootloops-lake']:
    p=subprocess.run([str(ROOT/n),'--version'],cwd=OUT,env=ENV,text=True,
        stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
    (OUT/(n+'-version.log')).write_text(p.stdout)
    assert p.returncode==0
    record[n+'_version']=p.stdout.strip()
(OUT/'lean-toolchain').write_bytes((HERE.parent/'integration/lean-toolchain').read_bytes())
(OUT/'TrueControl.lean').write_text('import Std\nexample : (2 : Nat) + 3 = 5 := by decide\n')
(OUT/'FalseControl.lean').write_text('import Std\nexample : (2 : Nat) + 3 = 6 := by decide\n')
assert run('TrueControl').returncode==0
p=run('FalseControl')
assert p.returncode!=0 and 'is false' in p.stdout
record['controls'].update(known_true='ACCEPTED',known_false='REJECTED')
for n in MODS:
    p=run(n,True)
    assert p.returncode==0 and not re.search(r'error:|sorryAx|declaration uses .sorry.',p.stdout),(n,p.stdout)
    if n=='GraphControls':
        p=run('GraphFalseControls')
        assert p.returncode!=0 and p.stdout.count('is false')==4,p.stdout
        record['controls']['pinned_graph_false_claims']='REJECTED_4_OF_4'

inventory='''import CompletionConsumers
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
p=run('ModuleInventory')
assert p.returncode==0,p.stdout
def parse(s):
    origins=re.findall(r'^MODULE\|([^|]+)\|(.+)$',s,re.M)
    axioms=re.findall(r'^MODAUDIT\|([^|]+)\|([^\n]*)$',s,re.M)
    assert origins and len(origins)==len(axioms)==len(set(origins)),'missing/duplicate axiom record'
    assert {n for _,n in origins}=={n for n,_ in axioms},'missing axiom declaration'
    assert {m for m,_ in origins}==set(MODS),'missing/extra source module'
    paths=dict(re.findall(r'^PATH\|([^|]+)\|(.+)$',s,re.M))
    for mod,raw in paths.items():
        path=Path(raw).resolve()
        if mod in MODS: assert path==OUT/(mod+'.olean'),'wrong local module origin: '+mod
        else: assert path.is_relative_to(ROOT/'.runtime/elan/toolchains'),'non-toolchain dependency: '+raw
    assert all(m in paths for m in MODS),'missing source path'
    return origins,axioms,paths
origins,axioms,paths=parse(p.stdout)
for name,bad in [
    ('missing_axiom_record',re.sub(r'^MODAUDIT\|[^\n]+\n','',p.stdout,count=1,flags=re.M)),
    ('wrong_module_path',re.sub(r'^PATH\|StateRestriction\|[^\n]+','PATH|StateRestriction|/tmp/foreign.olean',p.stdout,flags=re.M)),
    ('wrong_module_origin',re.sub(r'^MODULE\|StateRestriction\|','MODULE|ForeignModule|',p.stdout,count=1,flags=re.M))]:
    (OUT/(name+'-corrupted.log')).write_text(bad)
    try: parse(bad)
    except AssertionError as err: record['controls'][name]='CAUGHT: '+str(err)
    else: raise AssertionError('corruption survived: '+name)
record['module_origin_counts']={n:sum(m==n for m,_ in origins) for n in MODS}
record['module_origin_total']=len(origins)
record['resolved_module_paths']=paths
record['axiom_union_observed']=sorted({x.strip() for _,xs in axioms for x in xs.split(',') if x.strip()})
assert set(record['axiom_union_observed'])<=ALLOWED
(OUT/'PlantModel.lean').write_text('namespace HiddenCherryPlant\naxiom borrowed : False\nend HiddenCherryPlant\n')
assert run('PlantModel',True).returncode==0
(OUT/'ModulePlantAudit.lean').write_text('import PlantModel\n'+inventory.replace('`CompletionConsumers]', '`CompletionConsumers, `PlantModel]'))
p=run('ModulePlantAudit')
assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM|HiddenCherryPlant.borrowed|HiddenCherryPlant.borrowed' in p.stdout
record['controls']['hidden_custom_axiom']='CAUGHT'
def check_snapshot(n):
    assert sha(OUT/(n+'.lean'))==record['input_hashes'][str(SOURCES[n].relative_to(ROOT))],'source pin mismatch: '+n
orig=(OUT/'Endpoint.lean').read_bytes()
(OUT/'Endpoint.lean').write_bytes(orig+b'\n-- deliberate source corruption\n')
try: check_snapshot('Endpoint')
except AssertionError as err:
    record['controls']['source_byte_corruption']='CAUGHT: '+str(err)
    (OUT/'source-corruption-receipt.txt').write_text(str(err)+'\n')
else: raise AssertionError('source corruption survived')
(OUT/'Endpoint-corrupted.txt').write_bytes((OUT/'Endpoint.lean').read_bytes())
(OUT/'Endpoint.lean').write_bytes(orig)
for n in MODS: check_snapshot(n)
for rel,h in record['input_hashes'].items(): assert sha(ROOT/rel)==h,'source changed during replay: '+rel
for rel,h in frozen_hashes.items(): assert sha(ROOT/rel)==h,'completed freeze changed during replay: '+rel
record.update(status='PASS_AUTHOR_KERNEL_REPLAY_COMPLETED_COMMON_CHERRY',
    common_cherry='CLOSED_UNVERIFIED',endpoint_embeddings='CLOSED_UNVERIFIED',
    no_larger_literal_agreement='CLOSED_UNVERIFIED',literal_contract_expand='CLOSED_UNVERIFIED',
    exact_additional_cost='CLOSED_UNVERIFIED',every_budget_equivalence='CLOSED_UNVERIFIED',
    strict_current_label_decrease='CLOSED_UNVERIFIED',first_unproved_common_cherry_consumer=None,
    next_acceptance='FRESH_NONAUTHOR_REVIEW_REQUIRED',source_priority='OPEN',full_algorithm='OPEN',runtime='OPEN')
record['module_inventory_sha256']=sha(OUT/'ModuleInventory.log')
save()
summary={k:v for k,v in record.items() if k not in ['builds','input_hashes','resolved_module_paths']}
summary['receipt']=str(OUT.relative_to(ROOT))
(ROOT/'research/rmaf/results'/('algorithm-universal233-state-cherry-'+STAMP+'.json')).write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
