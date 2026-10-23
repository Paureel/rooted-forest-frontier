#!/usr/bin/env python3
"""Actual imported library and fresh scientific binary/source provenance; not a library review."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');TC=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0';READY=P.parent/'sol-preparation-READY-v1/preparation'
def h(p):
 d=hashlib.sha256()
 with p.open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
mods=[json.loads(z[len('IMPORTS_JSON '):])for z in (P/'logs/metadata-ImportDependencyIdentity.log').read_text().splitlines()if z.startswith('IMPORTS_JSON ')]
assert len(mods)==1
old=json.loads((READY/'stdlib-dependency-identity-v1.json').read_text());baseline={r['module']:r for r in old['entries']};rows=[];missing=[];changed=[]
for n in mods[0]:
 rel=Path(*n.split('.'));local=(P/'src'/rel.with_suffix('.lean')).is_file();source=(P/'src'if local else TC/'src/lean')/rel.with_suffix('.lean');binary=(P/'build'if local else TC/'lib/lean')/rel.with_suffix('.olean');r={'module':n,'fresh_local':local,'source':None,'binaries':[]}
 if source.is_file():r['source']={'path':str(source),'bytes':source.stat().st_size,'sha256':h(source)}
 else:missing.append({'module':n,'kind':'source'})
 for f in [binary,Path(str(binary)+'.private'),Path(str(binary)+'.server')]:
  if f.is_file():r['binaries'].append({'path':str(f),'bytes':f.stat().st_size,'sha256':h(f)})
 if not binary.is_file():missing.append({'module':n,'kind':'binary'})
 if not local and n in baseline:
  b=baseline[n];oldhashes={z['path']:z['sha256']for z in b['binaries']}
  if r['source']['sha256']!=b['source']['sha256']or any(oldhashes.get(z['path'])!=z['sha256']for z in r['binaries']):changed.append(n)
 rows.append(r)
out={'all_pass':not missing and not changed,'imported_modules':len(rows),'fresh_local_modules':sum(r['fresh_local']for r in rows),'standard_library_modules':sum(not r['fresh_local']for r in rows),'missing':missing,'changed_against_READY':changed,'entries':rows,'native_lean_sha256':h(TC/'bin/lean'),'standard_libraries_rebuilt':False,'standard_libraries_reviewed':False,'scientific_CoreGraph_rebuilt_from_pinned_source':True,'copied_scientific_oleans':0,'replication_increment':0}
(P/'actual-imported-dependency-identity-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='entries'},indent=2));assert out['all_pass']
