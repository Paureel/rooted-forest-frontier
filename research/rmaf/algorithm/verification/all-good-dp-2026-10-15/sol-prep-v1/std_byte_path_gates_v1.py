#!/usr/bin/env python3
"""One-shot Std-only exact byte/path gate with actual shadow-module corrupt twin."""
import hashlib,json,os,pathlib,shutil,subprocess,time
H=pathlib.Path(__file__).resolve().parent;ROOT=H.parents[5];LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean';B=H/'toy-fixed-v5';S=H/'shadow-path-v1';logs=H/'byte-path-logs';logs.mkdir(exist_ok=True)
def exact(got,want,label):
 if got!=want:raise AssertionError({'check':label,'got':got,'expected':want})
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 start=time.perf_counter();records=[];spec=json.loads((H/'INSTRUMENTS-MANIFEST-v1.json').read_text());expected=next(r['sha256'] for r in spec['files'] if r['path']=='toys/ToyClean.lean');assert B.exists()
 def run(label,args,path):
  t=time.perf_counter();r=subprocess.run([str(LEAN),*args],cwd=B if label!='compile-shadow' else S,env={**os.environ,'LEAN_PATH':path},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60)
  (logs/(label+'.log')).write_text(r.stdout);records.append({'label':label,'exit':r.returncode,'seconds':time.perf_counter()-t});assert r.returncode==0,{'label':label,'log':str(logs/(label+'.log'))};return r.stdout
 exact(digest(B/'ToyClean.lean'),expected,'clean source bytes')
 shutil.copyfile(H/'PathProbe.lean',B/'PathProbe.lean')
 clean=run('clean-path',['PathProbe.lean'],str(B));cleanpath=next(l.split('\t',1)[1] for l in clean.splitlines() if l.startswith('PATH\t'));exact(cleanpath,str((B/'ToyClean.olean').resolve()),'clean resolved module path')
 S.mkdir(exist_ok=False);source=(H/'toys/ToyClean.lean').read_text();assert source.count(':= 7')==1;(S/'ToyClean.lean').write_text(source.replace(':= 7',':= 8'))
 run('compile-shadow',['-o','ToyClean.olean','ToyClean.lean'],str(S))
 catches=[]
 try:exact(digest(S/'ToyClean.lean'),expected,'shadow source byte drift')
 except AssertionError as e:catches.append({'id':'source-byte-drift','caught':True,'finding':str(e)})
 else:raise AssertionError('byte drift survived')
 shadow=run('shadow-path',['PathProbe.lean'],str(S)+os.pathsep+str(B));shadowpath=next(l.split('\t',1)[1] for l in shadow.splitlines() if l.startswith('PATH\t'))
 try:exact(shadowpath,str((B/'ToyClean.olean').resolve()),'shadow resolved module path')
 except AssertionError as e:catches.append({'id':'wrong-resolved-path','caught':True,'finding':str(e)})
 else:raise AssertionError('wrong resolved path survived')
 exact(len(catches),2,'byte/path catch denominator');out={'status':'STD-BYTE-PATH-PASS','cleanResolvedPath':cleanpath,'corruptResolvedPath':shadowpath,'catches':catches,'processes':records,'seconds':time.perf_counter()-start};(H/'std-byte-path-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'corruptionsCaught':len(catches),'seconds':out['seconds']}))
if __name__=='__main__':main()
