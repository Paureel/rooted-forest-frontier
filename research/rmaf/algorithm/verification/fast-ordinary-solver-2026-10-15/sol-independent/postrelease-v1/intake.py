"""Exact release identity/contact check; no candidate source execution."""
import datetime,hashlib,json,pathlib,signal,time
signal.alarm(59)
HERE=pathlib.Path(__file__).resolve().parent
OWN=HERE.parent
ROOT=OWN.parents[5]
def sha(p):
 h=hashlib.sha256()
 with pathlib.Path(p).open('rb') as f:
  for x in iter(lambda:f.read(65536),b''):h.update(x)
 return h.hexdigest()
def main():
 begun=time.perf_counter()
 ready=OWN/'READY-v1.json'
 assert sha(ready)=='9cfaa653f84caf2bae44bdefa4b976500c10c69c7095cb99b5401becaaa55dc1'
 rr=json.loads(ready.read_text());n=0
 for r in rr['owned_files']+rr['installed_runtime_trust_pins']:
  p=pathlib.Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p);n+=1
 for p,h in rr['licensed_project_pins'].items():assert sha(ROOT/p)==h
 release=ROOT/'research/rmaf/algorithm/verification/fast-ordinary-solver-2026-10-15/ROOT-RELEASE-v1.json'
 assert sha(release)=='7b76b8313f55c1425dd900461bf836699ef91f0903582a1e4a7752b6fd7be48a'
 rel=json.loads(release.read_text());m=rel['licensed_candidate_packages'][0]
 p=ROOT/m['manifest'];assert sha(p)==m['sha256']
 contact=datetime.datetime.now(datetime.timezone.utc).isoformat()
 manifest=json.loads(p.read_text())
 summary={'utc_first_candidate_manifest':contact,'ready_pins_matched':n,'manifest_path':str(p),
 'manifest_sha256':m['sha256'],'schema':{k:({'type':type(v).__name__,'length':len(v)} if isinstance(v,(dict,list,str)) else v) for k,v in manifest.items()},'seconds':time.perf_counter()-begun}
 (HERE/'INTAKE-SCHEMA-v1.json').write_text(json.dumps(summary,indent=2)+'\n')
 print(json.dumps(summary,sort_keys=True))
if __name__=='__main__':main()
