#!/usr/bin/env python3
"""Independent isolated rebuild of exact released canonical scientific sources."""
import argparse,hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');P=Path(__file__).resolve().parent
CANON=ROOT/'results/algorithm-universal233-pair-assembly-20261015T093218Z'
LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def prepare():
 cert=json.loads((CANON/'certificate.json').read_text());order=cert['positive_order'];manifest=json.loads((ROOT/'research/rmaf/algorithm/universal233/pair_assembly/PAIR-ASSEMBLY-MANIFEST-v1.json').read_text());allowed={e['path']:e['sha256'] for e in manifest['immutable_files']};inputs={z['module']:z for z in cert['source_inputs']};records=[];done={'Std','Lean'}
 for m in order:
  src=CANON/(m+'.lean');rel=str(src.relative_to(ROOT));assert rel in allowed and h(src)==allowed[rel]==inputs[m]['compiled_sha256']
  body=src.read_text();imports=[]
  for line in body.splitlines():
   if line.startswith('import '):imports+=line[7:].split()
  if not all(x in done for x in imports):raise RuntimeError('Non-topological or unapproved dependency '+m+' '+repr(imports))
  dst=P/'src'/src.name;shutil.copyfile(src,dst);assert h(dst)==h(src);done.add(m)
  records.append({'module':m,'canonical_source':rel,'source_sha256':h(src),'imports':imports,'source_unchanged':True})
 (P/'source-adoption-v1.json').write_text(json.dumps({'modules':records,'denominator':len(records),'copied_scientific_oleans':0,'proof_body_edits':0},indent=2)+'\n')
 return order
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('stage',choices=['pilot','remaining']);a=ap.parse_args();order=prepare();selected=order[:4] if a.stage=='pilot' else order[4:];runs=[];start=time.perf_counter()
 for m in selected:
  env=os.environ.copy();env['LEAN_PATH']=str(P/'build');cmd=[str(LEAN),'-o',str(P/'build'/(m+'.olean')),m+'.lean'];t=time.perf_counter();r=subprocess.run(cmd,cwd=P/'src',env=env,text=True,capture_output=True);secs=time.perf_counter()-t
  (P/'logs'/('build-'+m+'.log')).write_text(r.stdout+r.stderr);runs.append({'module':m,'seconds':secs,'exit_code':r.returncode,'source_sha256':h(P/'src'/(m+'.lean')),'olean_sha256':h(P/'build'/(m+'.olean')) if (P/'build'/(m+'.olean')).exists() else None})
  out={'stage':a.stage,'denominator':len(selected),'completed':len(runs),'runs':runs,'seconds':time.perf_counter()-start,'all_pass':len(runs)==len(selected) and all(x['exit_code']==0 for x in runs),'LEAN_PATH':str(P/'build'),'scientific_oleans_copied':0}
  (P/('build-'+a.stage+'-v1.json')).write_text(json.dumps(out,indent=2)+'\n')
  if r.returncode:print(json.dumps(out,indent=2));raise SystemExit(1)
 print(json.dumps(out,indent=2))
