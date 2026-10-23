#!/usr/bin/env python3
"""One-shot source-bound isolated author replay and fail-closed audit.

Uses completed assembly-v1/source-coverage/cut source receipts as declared
development dependencies. The toolkit lacks a Lean module-origin audit; this
wraps the completed audit design rather than creating a competing solver.
"""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, time

D=Path(__file__).resolve().parent
U=D.parent
ROOT=D.parents[4]
STAMP=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT=ROOT/'results'/('algorithm-universal233-rank-replay-'+STAMP)
OUT.mkdir()
FROZEN=U/'assembly/replay/20261015T084051Z'
prior=json.loads((FROZEN/'certificate.json').read_text())
order=prior['positive_order'].copy()
sources=[]
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def check_pin(p,h):
    if digest(p)!=h: raise AssertionError('SOURCE_PIN_MISMATCH: '+str(p))
def check_manifest(p):
    m=json.loads(p.read_text())
    rows=m.get('immutable_files')
    if rows is None:
        rows=[{'path':k,'sha256':v} for k,v in (m['owned_files']|m['exact_source_import_pins']).items()]
    for r in rows: check_pin(ROOT/r['path'],r['sha256'])
    return {'path':str(p.relative_to(ROOT)),'sha256':digest(p),'pinned_files':len(rows)}
manifest_paths=[U/'source_coverage/SOURCE-COVERAGE-MANIFEST-v1.json',U/'cut_realization/CUT-REALIZATION-MANIFEST-v1.json',U/'assembly/ASSEMBLY-MANIFEST-v1.json']
checks=[check_manifest(p) for p in manifest_paths]
for row in prior['source_inputs']:
    check_pin(ROOT/row['source'],row['source_sha256'])
    check_pin(FROZEN/(row['compiled_module']+'.lean'),row['compiled_sha256'])
for name in order:
    p=FROZEN/(name+'.lean')
    (OUT/p.name).write_bytes(p.read_bytes())
    sources.append({'source':str(p.relative_to(ROOT)),'module':name,'compiled_module':name,'source_sha256':digest(p),'compiled_sha256':digest(p),'adapter':None})
for name in ['RankCost','MinimumUnique','TailMass','ColorClasses','Regression','RankControls']:
    original='Controls' if name=='RankControls' else name
    p=D/(original+'.lean')
    (OUT/(name+'.lean')).write_bytes(p.read_bytes())
    order.append(name)
    sources.append({'source':str(p.relative_to(ROOT)),'module':original,'compiled_module':name,'source_sha256':digest(p),'compiled_sha256':digest(p),'adapter':'module filename only Controls -> RankControls' if name!=original else None})
false_data=(D/'FalseControls.lean').read_bytes()
assert false_data.startswith(b'import Controls\n')
(OUT/'FalseRankControls.lean').write_bytes(false_data.replace(b'import Controls\n',b'import RankControls\n',1))
(OUT/'lean-toolchain').write_bytes((ROOT/'research/rmaf/lean/lean-toolchain').read_bytes())
env=dict(os.environ,LEAN_PATH=str(OUT))
runs=[]
record={'status':'RUNNING_AUTHOR_REPLAY','all_three_main_algorithm_milestones':'OPEN','independent_acceptance':False,'source_inputs':sources,'upstream_manifest_checks':checks,'positive_order':order,'runs':runs,'preproof_controls_receipt':(D/'CONTROLS-RECEIPT.txt').read_text().strip(),'timing':{'prior_exact_stack_modules':45,'prior_exact_stack_seconds':sum(x['seconds'] for x in prior['runs'] if x['module'] in prior['positive_order']),'new_module_development_max_seconds':0.5,'projection_seconds':30,'projection_basis':'Exact same local 45-module stack measured 22.15s; six new modules individually measured below0.5s; source/hash scanning and audit extra.'},'contact_limitations':['Completed all-colored X0 declared development; census/373MB raw receipt not rerun/read.','Broad symbol search incidentally returned isolated line hits from forbidden stack copies; no file was opened or theorem imported from them. Proof dependencies are pinned completed modules only.']}
def save(): (OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def run(name,build=False):
    start=time.monotonic()
    args=[str(ROOT/'bootloops-lean')]+(['-o',str(OUT/(name+'.olean'))] if build else [])+[str(OUT/(name+'.lean'))]
    p=subprocess.run(args,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=45)
    (OUT/(name+'.log')).write_text(p.stdout)
    runs.append({'module':name,'exit':p.returncode,'seconds':time.monotonic()-start})
    save()
    return p
(OUT/'TrueControl.lean').write_text('theorem knownTrue : 2+2=4 := by decide\n')
assert run('TrueControl').returncode==0
for name in order:
    p=run(name,True)
    if p.returncode: raise SystemExit(p.stdout)
def inventory_text(modules,foreign=False):
    imports='\n'.join('import '+m for m in ['Regression','RankControls','AssemblyControls','Controls','CutControls']+(['PlantForeign'] if foreign else []))
    names=', '.join('`'+m for m in modules)
    return imports+'''\nimport Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := ['''+names+''']
 let ns := (((env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)).filter fun n =>
   match env.getModuleIdxFor? n with
   | some i => mods.contains env.header.moduleNames[i.toNat]!
   | none => false).eraseDups
 for n in ns do
   let some i := env.getModuleIdxFor? n | throwError "MISSING_MODULE_ORIGIN"
   logInfo m!"MODULE|{env.header.moduleNames[i.toNat]!}|{n}"
   let ax ← collectAxioms n
   logInfo m!"MODAUDIT|{n}|{ax.toList}"
   for a in ax do
     unless a == `propext || a == `Quot.sound || a == `Classical.choice do
       throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
'''
(OUT/'ModuleAudit.lean').write_text(inventory_text(order))
p=run('ModuleAudit')
assert p.returncode==0,p.stdout
mods=re.findall(r'^MODULE\|([^|]+)\|(.+)$',p.stdout,re.M)
axs=re.findall(r'^MODAUDIT\|([^|\n]+)\|\[([^\]]*)\]$',p.stdout,re.M)
def complete(m,a):
    return bool(m) and len(m)==len(a) and {n for _,n in m}=={n for n,_ in a} and {k for k,_ in m}==set(order)
assert complete(mods,axs)
assert not complete(mods,axs[1:])
union=sorted({x.strip() for _,s in axs for x in s.split(',') if x.strip()})
assert set(union)<={'propext','Quot.sound','Classical.choice'}
p=run('FalseRankControls')
assert p.returncode!=0 and p.stdout.count('is false')==2 and '⊢ False' in p.stdout,p.stdout
(OUT/'PlantForeign.lean').write_text('import Regression\nnamespace ForeignNamespace\nprivate axiom hidden : False\ntheorem wrapper : False := hidden\nend ForeignNamespace\n')
assert run('PlantForeign',True).returncode==0
(OUT/'PlantAudit.lean').write_text(inventory_text(order+['PlantForeign'],True))
p=run('PlantAudit')
assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM' in p.stdout,p.stdout
plant=OUT/'SourcePinPlant.lean'
sample=OUT/'RankCost.lean'
plant.write_bytes(sample.read_bytes()+b'\n-- deliberate corruption\n')
try: check_pin(plant,digest(sample))
except AssertionError: source_plant=True
else: raise AssertionError('source pin mutation survived')
for row in sources:
    check_pin(ROOT/row['source'],row['source_sha256'])
    check_pin(OUT/(row['compiled_module']+'.lean'),row['compiled_sha256'])
for p in manifest_paths: check_manifest(p)
record.update({'status':'PASS_AUTHOR_SOURCE_BOUND_REPLAY','positive_source_modules':len(order),'module_origin_declarations':len(mods),'module_counts':{m:sum(k==m for k,_ in mods) for m in order},'axiom_union_observed':union,'preproof_positive_statements':len(re.findall(r'^theorem ',(D/'Controls.lean').read_text(),re.M)),'false_propositions_rejected':3,'missing_record_plant_caught':True,'foreign_private_axiom_plant_caught':True,'source_pin_plant_caught':source_plant,'meaning':'Actual feasible-rank unique literal output and exact color class memberships; actual infeasible-rank stronger cost; actual raw-LIST tail mass and2*b^-r corollary. Author evidence; fresh nonauthor/interface review and full algorithm remain OPEN.'})
save()
(OUT/'VERDICT.txt').write_text('PASS author source-bound replay: '+str(len(order))+'modules; '+str(len(mods))+'full-origin declarations;3 false propositions and3 audit corruption plants caught. Fresh review/full algorithm OPEN.\n')
(D/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
print('PASS author source-bound rank replay',len(order),'modules',len(mods),'declarations')
print(OUT)
