from pathlib import Path
from hashlib import sha256
import subprocess,os,json,time,argparse
H=Path(__file__).resolve().parent;ROOT=H.parents[5];B=H/'isolated';LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--pilot',action='store_true');args=ap.parse_args();a=json.loads((H/'SOURCE-ADOPTION-v1.json').read_text());order=a['order'][:5] if args.pilot else a['order'][5:];start=time.perf_counter();records=[];logs=H/'build-logs';logs.mkdir(exist_ok=True)
 for n in order:
  e=next(x for x in a['mapping'] if x['module']==n);assert sha256((B/(n+'.lean')).read_bytes()).hexdigest()==e['sha256']
  t=time.perf_counter();r=subprocess.run([str(LEAN),'-o',n+'.olean',n+'.lean'],cwd=B,env={**os.environ,'LEAN_PATH':str(B)},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60);(logs/(n+'.log')).write_text(r.stdout)
  rec={'module':n,'exit':r.returncode,'seconds':time.perf_counter()-t,'sourceSHA256':e['sha256']};records.append(rec);print(json.dumps(rec),flush=True)
  assert r.returncode==0,(n,r.stdout)
 out={'status':'SOURCE-REBUILD-PASS','pilot':args.pilot,'records':records,'seconds':time.perf_counter()-start,'scientificOleansCopied':False};(H/('build-pilot-v1.json' if args.pilot else 'build-fixed-v1.json')).write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
