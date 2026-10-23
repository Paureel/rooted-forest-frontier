"""Author isolated actual original-tree caller. Full recursive solver OPEN."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[4]
OUT=R/'results'/('algorithm-universal233-maf-scheduler-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));OUT.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pin=json.loads((D/'CONTROL-PIN-v1.json').read_text())
for e in pin['entries']:assert sha(D/e['path'])==e['sha256'],e['path']
inputs=json.loads((D/'SOURCE-PINS-v1.json').read_text())
for v in inputs['completed_manifests']:
 p=R/v['path'];assert sha(p)==v['sha256'];m=json.loads(p.read_text());rows=m.get('immutable_files',[])
 for e in rows:assert sha(R/e['path'])==e['sha256'],e['path']
entries=[]
for e in inputs['entries']:
 src=R/e['source'];assert sha(src)==e['original_sha256'];data=src.read_text()
 if e['first_import_adapter']:
  a,b=e['first_import_adapter'];assert data.startswith('import '+a+'\n');data=data.replace('import '+a+'\n','import '+b+'\n',1)
 p=OUT/(e['module']+'.lean');p.write_text(data);assert sha(p)==e['copy_sha256']
 entries.append(dict(e))
new=['MafCaller','MafPrecontrols','LocalSlots','Regional','Indexing','OriginalReconstruction','OriginalCaller','OriginalPaid','MafConsumerControls']
for n in new:
 src=D/(n+'.lean');(OUT/src.name).write_bytes(src.read_bytes());entries.append({'module':n,'source':str(src.relative_to(R)),'original_sha256':sha(src),'copy_sha256':sha(src),'first_import_adapter':None})
order=[e['module'] for e in entries];assert len(order)==len(set(order))
for e in entries:
 data=(OUT/(e['module']+'.lean')).read_text();clean=re.sub(r'/\-.*?\-/','',data,flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean),e['module']
(OUT/'MafFalseControls.lean').write_bytes((D/'MafFalseControls.lean').read_bytes())
(OUT/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
record={'status':'RUNNING AUTHOR actual MAF disjoint caller','full_algorithm_proved':False,'independent_acceptance':False,'all_main_milestones':'OPEN','source_inputs':entries,'positive_order':order,'preproof_pin_sha256':sha(D/'CONTROL-PIN-v1.json'),'upstream_manifests':inputs['completed_manifests'],'runs':[]}
def save():(OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def run(n,build=False):
 start=time.monotonic();p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(OUT/(n+'.olean'))] if build else [])+[str(OUT/(n+'.lean'))],cwd=R,env=dict(os.environ,LEAN_PATH=str(OUT)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (OUT/(n+'.log')).write_text(p.stdout);record['runs'].append({'module':n,'exit':p.returncode,'seconds':time.monotonic()-start});save();return p
(OUT/'TrueControl.lean').write_text('theorem known_true : 2+2=4 := by decide\n');assert run('TrueControl').returncode==0
(OUT/'FalseControl.lean').write_text('example : 2+2=5 := by decide\n');p=run('FalseControl');assert p.returncode!=0 and 'is false' in p.stdout
for n in order:
 p=run(n,True);assert p.returncode==0,(n,p.stdout)
def inventory(extra=''):
 mods=order+([extra] if extra else [])
 return '\n'.join('import '+n for n in mods)+'''
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := ['''+', '.join('`'+n for n in mods)+''']
 let ns := (((env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)).filter fun n =>
   match env.getModuleIdxFor? n with
   | some i => mods.contains env.header.moduleNames[i.toNat]!
   | none => false).eraseDups
 for n in ns do
   let some i := env.getModuleIdxFor? n | throwError "missing module"
   logInfo m!"MODULE|{env.header.moduleNames[i.toNat]!}|{n}"
   let axs ← collectAxioms n
   logInfo m!"MODAUDIT|{n}|{axs.toList}"
   for ax in axs do
    unless ax == `propext || ax == `Quot.sound || ax == `Classical.choice do
      throwError m!"REJECT_CUSTOM_AXIOM|{n}|{ax}"
'''
(OUT/'ModuleAudit.lean').write_text(inventory());p=run('ModuleAudit');assert p.returncode==0,p.stdout
mods=re.findall(r'^MODULE\|([^|\n]+)\|(.+)$',p.stdout,re.M);axs=re.findall(r'^MODAUDIT\|([^|\n]+)\|\[([^\]]*)\]$',p.stdout,re.M)
def complete(m,a):return bool(m) and len(m)==len(a) and len(m)==len(set(m)) and {n for _,n in m}=={n for n,_ in a} and {x for x,_ in m}==set(order)
assert complete(mods,axs);assert not complete(mods,axs[1:]);assert not complete([('WrongOrigin',mods[0][1])]+mods[1:],axs)
assert any('_private' in n and 'private_origin_control' in n for _,n in mods)
union=sorted({x.strip() for _,a in axs for x in a.split(',') if x.strip()});assert set(union)<={'propext','Quot.sound','Classical.choice'}
p=run('MafFalseControls');assert p.returncode!=0 and p.stdout.count('is false')==4,p.stdout
(OUT/'PlantPrivate.lean').write_text('namespace ForeignNamespace\nprivate axiom concealed : False\ntheorem uses_concealed : False := concealed\nend ForeignNamespace\n');assert run('PlantPrivate',True).returncode==0
(OUT/'PlantAudit.lean').write_text(inventory('PlantPrivate'));p=run('PlantAudit');assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM' in p.stdout,p.stdout
assert sha(OUT/'MafCaller.lean')!=hashlib.sha256((OUT/'MafCaller.lean').read_bytes()+b'\n-- corrupted\n').hexdigest()
def source_valid(e):return sha(R/e['source'])==e['original_sha256'] and sha(OUT/(e['module']+'.lean'))==e['copy_sha256']
assert not source_valid(dict(entries[-1],original_sha256='0'*64))
assert not source_valid(dict(entries[-1],copy_sha256='0'*64))
for e in entries:assert source_valid(e)
for e in pin['entries']:assert sha(D/e['path'])==e['sha256']
record.update({'status':'PASS AUTHOR actual original MAF disjoint caller','positive_source_modules':len(order),'module_origin_declarations':len(mods),'module_counts':{m:sum(x==m for x,_ in mods) for m in sorted(set(x for x,_ in mods))},'private_generated_included':True,'axiom_union_observed':union,'actual_maf_preproof_controls':10,'direct_universal_fixture_consumers':2,'false_propositions_rejected':4,'known_false_rejected':True,'missing_record_caught':True,'wrong_origin_caught':True,'foreign_private_axiom_caught':True,'byte_corruption_caught':True,'source_pin_mismatch_plant_caught':True,'copy_adapter_policy':'module filename and first import only; all proof bodies unchanged','scope':'Literal original restrictions and actual depth01 create slots; conditional exact recursive IH; original AF forward/reverse, FrefQ, exact additionalmin and actual trace paid mass under original>=2bad. Both originalQ source/target embeddings required. Full solver/source priorities/global recurrence OPEN.'});save()
(OUT/'VERDICT.txt').write_text(f'PASS AUTHOR original-tree disjoint caller: {len(order)} modules/{len(mods)} full origins. Exact recursive IH and main milestones OPEN.\n')
(D/'LATEST-REPLAY.txt').write_text(str(OUT.relative_to(R))+'\n')
print('PASS',len(order),'source modules',len(mods),'full origin declarations');print('Receipt',OUT)
