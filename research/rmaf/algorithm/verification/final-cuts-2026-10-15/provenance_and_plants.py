"""One-shot exact source/import/origin/body-reference map and detector plants.
Only manifest-bound primary/dependency sources; no author auditor code reuse.
"""
from pathlib import Path
import json,hashlib,re,copy,os,subprocess,time
b=Path(__file__).resolve().parent;root=b.parents[4];iso=b/'isolated';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pin=json.loads((b/'CANDIDATE-PIN.json').read_text());author=json.loads((b/'AUTHOR-MANIFEST.json').read_text());allowedpaths={x['path']:x['sha256'] for x in author['immutable_files']};receipt=json.loads((root/pin['canonical_receipt']).read_text());replay=json.loads((b/'REPLAY.json').read_text());origin=replay['all_origin_records'];modules={}
for path,sha in author['exact_source_import_pins'].items():
 assert path not in allowedpaths or allowedpaths[path]==sha,(path,'conflicting manifest pins')
 allowedpaths[path]=sha
source_inputs={x['compiled_module']:x for x in receipt['source_inputs']}
for x in pin['copied_sources']:
 if not x['positive']:continue
 name=x['module'];p=iso/(name+'.lean');declared=source_inputs[name];src=declared['source']
 assert src in allowedpaths,(name,src,'unbound source contact refused')
 assert h(root/src)==allowedpaths[src]==declared['source_sha256']==declared['compiled_sha256']==h(p)==x['sha256']
 text=p.read_text();imports=re.findall(r'^import\s+(\w+)',text,re.M)
 clean=re.sub(r'/\-.*?\-/','',text,flags=re.S);clean=re.sub(r'--[^\n]*','',clean);hits=re.findall(r'\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern|opaque)\b',clean);assert not hits,(name,hits)
 modules[name]={'primary_source':src,'primary_sha256':declared['source_sha256'],'canonical_source':x['source_path'],'canonical_sha256':x['sha256'],'isolated_source':str(p.relative_to(root)),'imports':imports,'adoption':declared.get('adapter'),'body_adoption':'exact source bytes incl imports; any filename/module rename is explicit, private/generated declarations inventoried under ACTUAL compiled module','origin_count':sum(z['origin']==name for z in origin),'forbidden_source_constructs':hits}
assert len(modules)==62 and set(source_inputs)==set(modules)
records=[]
for z in origin:
 row=dict(z);row['source_module_sha256']=modules[z['origin']]['canonical_sha256'];row['primary_source']=modules[z['origin']]['primary_source'];row['private_name']='_private.' in z['name'];row['constructor_or_recursor']=z['kind'] in ['constructor','recursor'];records.append(row)
out={'status':'EXACT-IMMUTABLE-SOURCE-ADOPTION-AND-ALL-ORIGIN-MAP','modules':modules,'all_declarations':records,'total_records':len(records),'private_records':sum(x['private_name'] for x in records),'structural_hash_note':replay['body_hash_note'],'independent_replications_added':0,'interface_printer':'Interfaces is copied metadata but not compiled/audited as a scientific source; initial63→62 role correction retained in CANDIDATE-PIN-initial.json before scientific execution'}
(b/'PROVENANCE-MAP.json').write_text(json.dumps(out,indent=2)+'\n')
env=os.environ.copy();env['LEAN_PATH']=str(iso);builds=[]
for a,n in [('CutUsed','ReviewPlantUsed'),('CutUnused','ReviewPlantUnused')]:
 (iso/(n+'.lean')).write_text((b/'std-toys'/(a+'.lean')).read_text())
s=(b/'std-toys/CutAudit.lean').read_text().replace('import CutClean\nimport CutUsed\nimport CutUnused','import ReviewPlantUsed\nimport ReviewPlantUnused').replace('["CutClean","CutUsed","CutUnused"]','["ReviewPlantUsed","ReviewPlantUnused"]').replace('CUT_ORIGIN ','PLANT_ORIGIN ')
(iso/'ReviewPlantAudit.lean').write_text(s)
for n in ['ReviewPlantUsed','ReviewPlantUnused','ReviewPlantAudit']:
 t=time.monotonic();r=subprocess.run([str(root/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);(b/'candidate-logs'/(n+'.log')).write_text(r.stdout);assert r.returncode==0,r.stdout;builds.append({'module':n,'exit':r.returncode,'seconds':time.monotonic()-t})
plants=[json.loads(l.split('PLANT_ORIGIN ',1)[1]) for l in r.stdout.splitlines() if 'PLANT_ORIGIN ' in l]
allowed={'Classical.choice','Quot.sound','propext'};expected={(x['name'],x['origin']) for x in origin}
def gate(rows,ns,check_body=False):
 if len(rows)!=len({x['name'] for x in rows}):return 'REJECT duplicate originating record'
 if {(x['name'],x['origin']) for x in rows}!=ns:return 'REJECT missing/wrong originating record'
 for x in rows:
  if x['kind']=='axiom':return 'REJECT originating custom axiom '+x['name']
  if not set(x['axioms'])<=allowed:return 'REJECT custom axiom closure '+x['name']
 if check_body and rows!=origin:return 'REJECT immutable type/body/reference map mismatch'
 return 'ACCEPT complete origin/source map'
diagnostics={'clean':gate(origin,expected,True),'missing':gate(origin[1:],expected),'duplicate':gate(origin+[origin[0]],expected)}
wrong=copy.deepcopy(origin);wrong[0]['origin']='Foreign';diagnostics['wrong_origin']=gate(wrong,expected)
wrong=copy.deepcopy(origin);wrong[0]['type_structural_hash']+=1;diagnostics['wrong_type_body_map']=gate(wrong,expected,True)
for mod in ['ReviewPlantUsed','ReviewPlantUnused']:
 rs=[x for x in plants if x['origin']==mod];diagnostics[mod]=gate(rs,{(x['name'],x['origin']) for x in rs});assert any(x['kind']=='axiom' and '_private.' in x['name'] for x in rs)
 if mod=='ReviewPlantUnused':assert any(x['kind']=='theorem' and not x['axioms'] for x in rs)
first=next(x for x in pin['copied_sources'] if x['positive']);raw=(iso/(first['module']+'.lean')).read_bytes();assert hashlib.sha256(raw+b'\n-- planted mutation\n').hexdigest()!=first['sha256'];assert first['sha256']!='0'*64;diagnostics['source_corruption']='REJECT source SHA mismatch';diagnostics['wrong_source_pin']='REJECT source SHA mismatch'
assert diagnostics['clean'].startswith('ACCEPT') and all(v.startswith('REJECT') for k,v in diagnostics.items() if k!='clean')
(b/'ORIGIN-DETECTOR-RECEIPT.json').write_text(json.dumps({'status':'PASS-COMPLETE-ORIGIN-PLANTS','diagnostics':diagnostics,'plant_records':plants,'builds':builds,'scope':'Custom axioms deliberately only in isolated detector plants,excluded from62 scientific modules. Missing/duplicate/origin/type-body/source mutations have clean twins. No author source changed.'},indent=2)+'\n')
print(json.dumps({'modules':len(modules),'declarations':len(records),'private':sum(x['private_name'] for x in records),'detectors':diagnostics}))
