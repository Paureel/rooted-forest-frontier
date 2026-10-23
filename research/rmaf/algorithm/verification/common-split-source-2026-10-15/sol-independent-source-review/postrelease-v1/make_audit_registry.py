#!/usr/bin/env python3
"""Bind own source-before-build registry to retained cold outputs and raw imports."""
import hashlib,json,pathlib
P=pathlib.Path(__file__).resolve().parent
def h(v):return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
def bh(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def nm(s):
 a=['anonymous']
 for p in s.split('.'):a=['str',a,p]
 return a
def run(tag):
 sources=json.loads((P/'COLD-SOURCE-REGISTRY-v1.json').read_text())
 builds={x['module']:x for x in map(json.loads,(P/'BUILD-RESULTS.jsonl').read_text().splitlines())}
 assert len(builds)==len(sources)==151 and all(x['code']==0 for x in builds.values())
 head=json.loads((P/'SOURCE-HEADER-AUDIT-v1.json').read_text())['imports']
 modules={};checks=[]
 for s in sources:
  m=s['module'];b=builds[m];assert b['source_sha256']==s['source_sha256']==bh(s['source']);assert b['olean_sha256']==bh(s['olean'])
  records={};p=P/'producer-rows'/(m+'.jsonl')
  if p.exists():
   with p.open('rb') as f:
    for line in f:
     r=json.loads(line)
     if r['record']!='producer_part':continue
     header=[{'module':'Init','all':False},{'module':'Init','all':False}]+head[m]
     expected=[{'module':nm(v['module']),'module_text':v['module'],'import_all':v['all'],'is_exported':True,'is_meta':i==1} for i,v in enumerate(header)]
     assert r['import_records']==expected,('source/compiler import discrepancy',m,r['import_records'],expected)
     records[str(r['part'])]=h(r['import_records']);checks.append({'module':m,'part':r['part'],'source_header_and_full_flags_equal':True,'sha256':records[str(r['part'])]})
  modules[m]={'source':s['source'],'source_sha256':s['source_sha256'],'olean':s['olean'],'olean_sha256':b['olean_sha256'],'observed_cold_import_record_hashes':records}
 old=json.loads((P.parent/'CONTROL-RESULTS-v7.json').read_text())
 std={x['path']:x['sha256'] for x in old['trusted_and_control_olean_pins'] if 'installed trusted standard-library' in x['scope']}
 root=next(q for q in P.parents if (q/'bootloops-python').exists());sys=root/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0'
 reg={'scientific_modules':modules,'trusted_olean_pins':std,'trusted_library_root':str(sys/'lib/lean'),'source_before_build_registry_sha256':bh(P/'COLD-SOURCE-REGISTRY-v1.json'),'build_results_sha256':bh(P/'BUILD-RESULTS.jsonl'),'trusted_std_source':'own prerelease pinned installed Lean/Std; not rebuilt','full_import_relation':checks}
 out=P/('ACTUAL-AUDIT-REGISTRY-'+tag+'.json');assert not out.exists();out.write_text(json.dumps(reg,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'registry':str(out),'source_modules':len(modules),'observed_producers':len(set(x['module'] for x in checks)),'standard_parts_pinned':len(std),'source_header_full_import_flag_checks':len(checks)}))
if __name__=='__main__':
 import sys;run(sys.argv[1])
