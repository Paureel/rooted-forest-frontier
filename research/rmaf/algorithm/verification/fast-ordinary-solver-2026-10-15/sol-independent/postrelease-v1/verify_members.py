"""Hash only the exact released member list; no author executable is run."""
import datetime,hashlib,json,pathlib,sys,time
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parent.parents[5]
MANIFEST=ROOT/'research/rmaf/algorithm/universal233/ordinary_dispatch/fast_ordinary_recursion/FINAL-MANIFEST-v1.json'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(65536),b''):h.update(c)
 return h.hexdigest()
def main():
 start=time.perf_counter();m=json.loads(MANIFEST.read_text());allrows=m['immutable_files']
 assert sha(MANIFEST)=='0f806c00eacdc8d3d12ffb9c38406edd0363eb6b5a235897506880fe05efcb8c'
 assert len(allrows)==4639
 mode=sys.argv[1];rows=allrows if mode=='full' else [allrows[i] for i in range(0,len(allrows),145)]
 total=0;durations=[];names=[]
 for r in rows:
  t=time.perf_counter();p=ROOT/r['path'];assert p.stat().st_size==r['bytes'],r['path'];assert sha(p)==r['sha256'],r['path']
  total+=r['bytes'];names.append(r['path']);durations.append(time.perf_counter()-t)
 result={'mode':mode,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'matched':len(rows),
 'declared_total':len(allrows),'bytes_hashed':total,'seconds':time.perf_counter()-start,'max_member_seconds':max(durations),
 'member_paths':names if mode=='full' else None,'scientific_acceptance':False}
 (HERE/f'MEMBER-IDENTITY-{mode}-v1.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='member_paths'},sort_keys=True))
if __name__=='__main__':main()
