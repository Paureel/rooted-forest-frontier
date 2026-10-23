import argparse,hashlib,json,os,pathlib,subprocess,time
P=pathlib.Path(__file__).resolve().parent;ROOT=P.parents[6];LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['pilot','full']);a=ap.parse_args();f=P/('Readouts_pilot_v2.lean' if a.mode=='pilot' else 'Readouts_v2.lean');env=dict(os.environ);env['LEAN_PATH']=str(P/'scientific-build');at=time.perf_counter();cmd=[str(LEAN),'--run',f.name];r=subprocess.run(cmd,cwd=P,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120);(P/('readouts-'+a.mode+'-v2.log')).write_text(r.stdout);report={'mode':a.mode,'seconds':time.perf_counter()-at,'command':cmd,'LEAN_PATH':env['LEAN_PATH'],'returncode':r.returncode,'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'rows':[],'trace':[]}
for line in r.stdout.splitlines():
 if line.startswith('{'):report['rows'].append(json.loads(line))
 elif line.startswith('TRACE|'):report['trace'].append(line.split('|')[1:])
(P/('readouts-'+a.mode+'-v2.json')).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['rows','trace']}));assert r.returncode==0,r.stdout[:5000]
