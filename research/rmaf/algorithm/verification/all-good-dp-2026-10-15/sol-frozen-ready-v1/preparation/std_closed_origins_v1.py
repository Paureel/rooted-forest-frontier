#!/usr/bin/env python3
"""One-shot exact imported-source universe gate, with non-Toy unused axiom plant."""
import hashlib,json,os,pathlib,shutil,subprocess,time
H=pathlib.Path(__file__).resolve().parent;ROOT=H.parents[5];B=H/'toy-fixed-v5';LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
def main():
 start=time.perf_counter();manifest=json.loads((H/'INSTRUMENTS-MANIFEST-v3.json').read_text());pins={r['path']:r['sha256'] for r in manifest['files']}
 for name in ['ClosedImports.lean','toys/HiddenAlien.lean','CONTROL-ORIGIN-AMENDMENT-v1.json','std_closed_origins_v1.py']:assert hashlib.sha256((H/name).read_bytes()).hexdigest()==pins[name]
 logs=H/'closed-origin-logs';logs.mkdir(exist_ok=True);records=[]
 def run(label,args,want):
  t=time.perf_counter();r=subprocess.run([str(LEAN),*args],cwd=B,env={**os.environ,'LEAN_PATH':str(B)},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60);(logs/(label+'.log')).write_text(r.stdout);records.append({'label':label,'exit':r.returncode,'seconds':time.perf_counter()-t});assert (r.returncode==0)==(want==0),{'label':label,'exit':r.returncode};return r.stdout
 shutil.copyfile(H/'ClosedImports.lean',B/'ClosedImports.lean');shutil.copyfile(H/'toys/HiddenAlien.lean',B/'HiddenAlien.lean')
 run('compile-exact-closure',['-o','ClosedImports.olean','ClosedImports.lean'],0);run('compile-hidden-alien',['-o','HiddenAlien.olean','HiddenAlien.lean'],0)
 (B/'ProbeClosedClean.lean').write_text('import ClosedImports\nimport ToyClean\n#closed_imports\n');(B/'ProbeClosedCorrupt.lean').write_text('import ClosedImports\nimport ToyClean\nimport HiddenAlien\n#closed_imports\n')
 clean=run('closed-clean',['ProbeClosedClean.lean'],0);assert 'CLOSED_IMPORTS_OK' in clean
 bad=run('closed-corrupt',['ProbeClosedCorrupt.lean'],1);assert 'unmapped source origin HiddenAlien' in bad;assert 'CLOSED_IMPORTS_OK' not in bad
 out={'status':'STD-EXACT-CLOSURE-PASS','cleanSourceModules':['ToyClean'],'corruptCatches':[{'id':'unmapped-non-Toy-unused-axiom-origin','caught':True,'module':'HiddenAlien'}],'processes':records,'seconds':time.perf_counter()-start};(H/'std-closed-origins-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'corruptionsCaught':len(out['corruptCatches']),'seconds':out['seconds']}))
if __name__=='__main__':main()
