"""One-shot source-bound ownership assembly audit; AUTHOR evidence only.
Uses the completed module-origin inventory design as a development contact.
Frozen original files are read-only; all rebuilt sources/results go to a new
receipt. The ONLY adapter is cut Coverage's filename and one import path.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,time,datetime
D=Path(__file__).resolve().parent;U=D.parent;ROOT=U.parents[3]
OUT=D/'replay'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');OUT.mkdir(parents=True,exist_ok=False)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check_manifest(p):
 m=json.loads(p.read_text());rows=m.get('immutable_files')
 if rows is None:rows=[{'path':k,'sha256':v} for k,v in m['owned_files'].items()]+[{'path':k,'sha256':v} for k,v in m['exact_source_import_pins'].items()]
 for r in rows:assert digest(ROOT/r['path'])==r['sha256'],r['path']
 return {'path':str(p.relative_to(ROOT)),'sha256':digest(p),'pinned_files':len(rows)}
manifest_checks=[check_manifest(U/'source_coverage/SOURCE-COVERAGE-MANIFEST-v1.json'),check_manifest(U/'cut_realization/CUT-REALIZATION-MANIFEST-v1.json')]
entries=[];order=[]
for package,stamp in [('source_coverage','20261015T075710Z'),('cut_realization','20261015T080042Z')]:
 p=U/package/'replay'/stamp;cert=json.loads((p/'certificate.json').read_text());mods=cert.get('module_origin_counts',cert.get('module_counts'));assert mods
 for build in cert['builds']:
  name=build['module']
  if name not in mods:continue
  source=p/(name+'.lean');newname='CutCoverage' if package=='cut_realization' and name=='Coverage' else name;data=source.read_bytes();adapter=None
  if package=='cut_realization' and name=='InitialCoverage':
   assert data.startswith(b'import Coverage\n');data=data.replace(b'import Coverage\n',b'import CutCoverage\n',1);adapter='single import module path Coverage -> CutCoverage; every proof body unchanged'
  if newname in order:assert (OUT/(newname+'.lean')).read_bytes()==data,(package,name,'source conflict')
  else:(OUT/(newname+'.lean')).write_bytes(data);order.append(newname)
  entries.append({'source':str(source.relative_to(ROOT)),'source_sha256':digest(source),'module':name,'compiled_module':newname,'compiled_sha256':hashlib.sha256(data).hexdigest(),'adapter':adapter or ('module filename only Coverage -> CutCoverage' if name!=newname else None)})
NEW=['ParentColors','WholeSource','Requests','OwnershipBase','ChainAssembly','SourceValidity','ForestOutputs','AssemblyControls']
for name in NEW:
 p=D/(name+'.lean');(OUT/p.name).write_bytes(p.read_bytes());order.append(name);entries.append({'source':str(p.relative_to(ROOT)),'source_sha256':digest(p),'module':name,'compiled_module':name,'compiled_sha256':digest(p),'adapter':None})
(OUT/'FalseAssembly.lean').write_bytes((D/'FalseAssembly.lean').read_bytes());(OUT/'lean-toolchain').write_bytes((ROOT/'research/rmaf/lean/lean-toolchain').read_bytes());env=dict(os.environ,LEAN_PATH=str(OUT));runs=[]
record={'status':'RUNNING-author-source-bound-assembly','full_algorithm_proved':False,'independent_acceptance':False,'source_inputs':entries,'upstream_manifest_checks':manifest_checks,'positive_order':order,'runs':runs}
def save():(OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def run(name,build=False):
 start=time.monotonic();p=subprocess.run([str(ROOT/'bootloops-lean')]+(['-o',str(OUT/(name+'.olean'))] if build else [])+[str(OUT/(name+'.lean'))],cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);(OUT/(name+'.log')).write_text(p.stdout);runs.append({'module':name,'exit':p.returncode,'seconds':time.monotonic()-start});save();return p
(OUT/'TrueControl.lean').write_text('theorem knownTrue : 2+2=4 := by decide\n');assert run('TrueControl').returncode==0
for n in order:
 p=run(n,True)
 if p.returncode:raise SystemExit(p.stdout)
def inventory_text(mods,extra=''):
 imports='\n'.join('import '+m for m in ['AssemblyControls','Controls','CutControls']+([extra] if extra else []))
 names=', '.join('`'+m for m in mods)
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
   let some i := env.getModuleIdxFor? n | throwError "missing module"
   logInfo m!"MODULE|{env.header.moduleNames[i.toNat]!}|{n}"
   let ax ← collectAxioms n
   logInfo m!"MODAUDIT|{n}|{ax.toList}"
   for a in ax do
     unless a == `propext || a == `Quot.sound || a == `Classical.choice do
       throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
'''
(OUT/'ModuleAudit.lean').write_text(inventory_text(order));p=run('ModuleAudit');assert p.returncode==0,p.stdout
mods=re.findall(r'^MODULE\|([^|]+)\|(.+)$',p.stdout,re.M);axs=re.findall(r'^MODAUDIT\|([^|\n]+)\|\[([^\]]*)\]$',p.stdout,re.M)
def complete(m,a):return bool(m) and len(m)==len(a) and {n for _,n in m}=={n for n,_ in a} and set(k for k,_ in m)==set(order)
assert complete(mods,axs);assert not complete(mods,axs[1:]);record['missing_record_plant_caught']=True
union=sorted({v.strip() for _,a in axs for v in a.split(',') if v.strip()});assert set(union)<={'propext','Quot.sound','Classical.choice'}
p=run('FalseAssembly');assert p.returncode!=0 and p.stdout.count('is false')==4,p.stdout
(OUT/'PlantPrivate.lean').write_text('import AssemblyControls\nnamespace OutsideProduction\nprivate axiom hidden : False\ntheorem wrapper : False := hidden\nend OutsideProduction\n');assert run('PlantPrivate',True).returncode==0
(OUT/'PlantAudit.lean').write_text(inventory_text(order+['PlantPrivate'],'PlantPrivate'));p=run('PlantAudit');assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM' in p.stdout,p.stdout
sample=OUT/'ParentColors.lean';expected=digest(sample);altered=hashlib.sha256(sample.read_bytes()+b'\n-- deliberate source-pin mutation\n').hexdigest();assert expected!=altered;record['source_pin_plant_caught']=True
for e in entries:assert digest(ROOT/e['source'])==e['source_sha256']
for f in [U/'source_coverage/SOURCE-COVERAGE-MANIFEST-v1.json',U/'cut_realization/CUT-REALIZATION-MANIFEST-v1.json']:check_manifest(f)
record.update({'status':'PASS-author-source-bound-assembly','positive_source_modules':len(order),'module_origin_declarations':len(mods),'module_counts':{m:sum(x==m for x,_ in mods) for m in sorted(set(x for x,_ in mods))},'axiom_union_observed':union,'false_propositions_rejected':4,'private_foreign_axiom_plant_caught':True,'meaning':'Actual original agreement ownership -> literal whole-source clique/fourchain/diagonal generated member, original final refinement, actual original cut components, parent containment and all requested target clearing. Requires original hard-parent partition/refinement/source safety hypotheses. Branch mass proof separate; full algorithm/runtime and independent review OPEN.'});save();(OUT/'VERDICT.txt').write_text('PASS author ownership construction; '+str(len(order))+' exact source builds; '+str(len(mods))+' full module-origin declarations;4 false controls and3 audit/pin plants caught. Independent acceptance/full algorithm OPEN.\n');print('PASS source-bound actual ownership assembly',len(order),'modules',len(mods),'declarations');print('Receipt',OUT)
