#!/usr/bin/env python3
"""One-shot exact-source author replay for final original-cut recovery.

Wraps the completed rank/cut/source/core-work receipt audit. This is a
problem-specific theorem integration, not a new generic audit toolkit.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
D=Path(__file__).resolve().parent
U=D.parent
ROOT=D.parents[4]
RANK=ROOT/'results/algorithm-universal233-rank-replay-20261015T091933Z'
CORE=ROOT/'results/algorithm-universal233-core-work-20261015T081612Z'
OUT=ROOT/'results'/('algorithm-universal233-final-cuts-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
OUT.mkdir()
ALLOWED={'Classical.choice','Quot.sound','propext'}
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if digest(p)!=h: raise AssertionError('SOURCE_PIN_MISMATCH: '+str(p))
def manifest(p):
 j=json.loads(p.read_text())
 rows=j.get('immutable_files')
 if rows is None: rows=[{'path':k,'sha256':v} for k,v in (j['owned_files']|j['exact_source_import_pins']).items()]
 for row in rows: pin(ROOT/row['path'],row['sha256'])
 return {'path':str(p.relative_to(ROOT)),'sha256':digest(p),'rows':len(rows)}
def clean(s):
 s=re.sub(r'/\-.*?\-/',lambda m:'\n'*m.group().count('\n'),s,flags=re.S)
 return re.sub(r'--[^\n]*','',s)
manifest_paths=[U/'rank_dichotomy/RANK-MANIFEST-v1.json',U/'core_work/CORE-WORK-MANIFEST-v1.json',U/'source_coverage/SOURCE-COVERAGE-MANIFEST-v1.json',U/'cut_realization/CUT-REALIZATION-MANIFEST-v1.json']
checks=[manifest(p) for p in manifest_paths]
rank=json.loads((RANK/'certificate.json').read_text())
core=json.loads((CORE/'certificate.json').read_text())
for row in rank['source_inputs']:
 pin(ROOT/row['source'],row['source_sha256'])
 pin(RANK/(row['compiled_module']+'.lean'),row['compiled_sha256'])
for rel,h in core['input_hashes'].items(): pin(ROOT/rel,h)
order=rank['positive_order'].copy()
sources=[]
def add(source,name,original=None,adapter=None):
 data=source.read_bytes()
 if re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(data.decode())):
  raise AssertionError('PROOF_ESCAPE: '+str(source))
 (OUT/(name+'.lean')).write_bytes(data)
 sources.append({'source':str(source.relative_to(ROOT)),'source_sha256':digest(source),'compiled_module':name,'compiled_sha256':digest(OUT/(name+'.lean')),'adapter':adapter})
for name in order: add(RANK/(name+'.lean'),name)
# Shared actual core proof bodies must match the already copied rank imports.
for name in ['RMAF','Geometry','Bridge','Composition','CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants','SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches']:
 assert (CORE/(name+'.lean')).read_bytes()==(OUT/(name+'.lean')).read_bytes(),('SHARED_SOURCE_DIVERGENCE',name)
for name in ['Work','Primitive','Payload','CoreWorkControls']:
 original='Controls' if name=='CoreWorkControls' else name
 add(U/'core_work'/(original+'.lean'),name,original,'filename only Controls -> CoreWorkControls' if name!=original else None)
 pin(CORE/(original+'.lean'),digest(U/'core_work'/(original+'.lean')))
 order.append(name)
for name in ['RecoveryProgram','BlockColors','Permutations','Recovery','FinalWork','FinalRecoveryControls','FinalRegression']:
 original={'FinalRecoveryControls':'Controls','FinalRegression':'Regression'}.get(name,name)
 add(D/(original+'.lean'),name,original,'filename only '+original+' -> '+name if original!=name else None)
 order.append(name)
for name in ['FalseControls']:
 (OUT/(name+'.lean')).write_bytes((D/(name+'.lean')).read_bytes())
(OUT/'lean-toolchain').write_bytes((ROOT/'research/rmaf/lean/lean-toolchain').read_bytes())
env=dict(os.environ,LEAN_PATH=str(OUT))
runs=[]
record={'runner_sha256':digest(Path(__file__)),'dependency_receipts':[{'path':str((RANK/'certificate.json').relative_to(ROOT)),'sha256':digest(RANK/'certificate.json')},{'path':str((CORE/'certificate.json').relative_to(ROOT)),'sha256':digest(CORE/'certificate.json')}],'rank_source_lineage':rank['source_inputs'],'core_source_lineage':core['input_hashes'],'status':'RUNNING_AUTHOR_SOURCE_BOUND_REPLAY','all_three_main_algorithm_milestones':'OPEN','independent_acceptance':False,'source_inputs':sources,'upstream_manifest_checks':checks,'positive_order':order,'runs':runs,'preproof_controls_receipt':(D/'CONTROLS-RECEIPT.txt').read_text().strip(),'timing':{'basis':'Same-host completed exact 51-module rank replay and 20-module core-work receipt; new development compiles individually below one second','prior_rank_positive_seconds':sum(r['seconds'] for r in rank['runs'] if r['module'] in rank['positive_order']),'prior_core_positive_seconds':sum(r['seconds'] for r in core['builds'] if r['module'] in [x['compiled_module'] for x in sources]),'planned_upper_seconds':60,'scaling':'one full source pass, no mathematical census'},'contact_limitations':['Only completed permitted development inputs were read. Broad filename searches returned paths to forbidden copies, never their bodies.','Finite controls and author replay are development evidence. Fresh nonauthor acceptance is required.'],'source_cost_qualification':'Exact value/size/color/envelope algebra is kernel checked; guard and helper-to-fine-operation source correspondence is the conservative mathematical argument in COST-MODEL.md.'}
def save(): (OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def run(name,build=False):
 start=time.monotonic();args=[str(ROOT/'bootloops-lean')]+(['-o',str(OUT/(name+'.olean'))] if build else [])+[str(OUT/(name+'.lean'))]
 p=subprocess.run(args,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (OUT/(name+'.log')).write_text(p.stdout);runs.append({'module':name,'exit':p.returncode,'seconds':round(time.monotonic()-start,6)});save();return p
(OUT/'TrueControl.lean').write_text('import Std\ntheorem knownTrue : (2:Nat)+2=4 := by decide\n')
(OUT/'FalseControl.lean').write_text('import Std\ntheorem knownFalse : (0:Nat)=1 := by decide\n')
assert run('TrueControl').returncode==0
p=run('FalseControl');assert p.returncode!=0 and 'is false' in p.stdout,p.stdout
for name in order:
 p=run(name,True)
 assert p.returncode==0 and 'declaration uses' not in p.stdout and 'sorryAx' not in p.stdout,(name,p.stdout)
# The authored false controls import only the executable program and actual model.
p=run('FalseControls');assert p.returncode!=0 and p.stdout.count('is false')==3,p.stdout

def inventory(modules,plant=False):
 imports='\n'.join('import '+x for x in ['FinalRegression','CoreWorkControls','Regression','RankControls','AssemblyControls','Controls','CutControls']+(['PlantForeign'] if plant else []))
 names=', '.join('`'+n for n in modules)
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
def parse(s,mods):
 m=re.findall(r'^MODULE\|([^|]+)\|(.+)$',s,re.M)
 a=re.findall(r'^MODAUDIT\|([^|\n]+)\|\[([^\]]*)\]$',s,re.M)
 assert m and len(m)==len(a) and len(m)==len(set(m))
 assert {n for _,n in m}=={n for n,_ in a}
 assert {k for k,_ in m}==set(mods)
 return m,a
(OUT/'ModuleAudit.lean').write_text(inventory(order))
p=run('ModuleAudit');assert p.returncode==0,p.stdout
m,a=parse(p.stdout,order)
try: parse(re.sub(r'^MODAUDIT\|[^\n]*\n','',p.stdout,count=1,flags=re.M),order)
except AssertionError: missing=True
else: raise AssertionError('MISSING_RECORD_PLANT_SURVIVED')
union=sorted({v.strip() for _,s in a for v in s.split(',') if v.strip()});assert set(union)<=ALLOWED,union
(OUT/'PlantForeign.lean').write_text('import FinalRegression\nnamespace ForeignNamespace\nprivate axiom hidden : False\ntheorem wrapper : False := hidden\nend ForeignNamespace\n')
assert run('PlantForeign',True).returncode==0
(OUT/'PlantAudit.lean').write_text(inventory(order+['PlantForeign'],True))
p=run('PlantAudit');assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM' in p.stdout,p.stdout
plant=OUT/'SourcePinPlant.lean';sample=OUT/'RecoveryProgram.lean'
plant.write_bytes(sample.read_bytes()+b'\n-- deliberate source corruption\n')
try: pin(plant,digest(sample))
except AssertionError: pinplant=True
else: raise AssertionError('SOURCE_PIN_PLANT_SURVIVED')
(OUT/'Interfaces.lean').write_text('import FinalRegression\n'+ '\n'.join('#check Universal233.FinalCutRecovery.'+n for n in ['recover','checked_rank','checked_separation','checked_block_permutation','agreement_block_permutation','recover_checked','recover_sound','recover_edges','recover_original_agreement','recover_success_iff','accepted_guards','meterRecover_value','meterColor_value','meterColor_work','total_color_work','final_work_bound','final_work_actual_cost','final_work_absorbed'])+'\n')
p=run('Interfaces');assert p.returncode==0,p.stdout
for row in sources:
 pin(ROOT/row['source'],row['source_sha256']);pin(OUT/(row['compiled_module']+'.lean'),row['compiled_sha256'])
for p in manifest_paths: manifest(p)
for row in rank['source_inputs']:pin(ROOT/row['source'],row['source_sha256'])
for rel,h in core['input_hashes'].items():pin(ROOT/rel,h)
pin(Path(__file__),record['runner_sha256'])
record.update(status='PASS_AUTHOR_SOURCE_BOUND_FINAL_CUT_RECOVERY',positive_source_modules=len(order),module_origin_declarations=len(m),module_counts={n:sum(k==n for k,_ in m) for n in order},axiom_union_observed=union,preproof_positive_statements=11,postproof_interface_regressions=5,false_propositions_rejected=4,missing_audit_record_plant_caught=missing,foreign_private_axiom_plant_caught=True,source_pin_corruption_plant_caught=pinplant,positive_compile_seconds=round(sum(r['seconds'] for r in runs if r['module'] in order),6),meaning='Executable final original-source recovery; exact |P|-1 original nonredundant cuts; full original residual component reconstruction; actual block/label permutation and original agreement transport; qualified source-operation final call bound. All main milestones OPEN.')
save()
(OUT/'VERDICT.txt').write_text('PASS author source-bound final cut recovery: '+str(len(order))+' modules; '+str(len(m))+' full module-origin declarations; 11 preproof actual controls; 4 rejected false propositions; missing-record/custom-axiom/source-pin corruption caught. Fresh nonauthor acceptance and all main milestones OPEN.\n')
if not (D/'FINAL-CUTS-MANIFEST-v1.json').exists():
 (D/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
print(record['status'],len(order),'modules',len(m),'declarations')
print(OUT)
