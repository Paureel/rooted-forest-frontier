import pathlib,json,subprocess,sys,os
n=pathlib.Path(__file__).resolve().parent
c=json.loads((n/'RUN-CONFIG-v1.json').read_text())
name=sys.argv[1];label=sys.argv[2]
assert name.replace('_','').isalnum()
args=[sys.executable,str(n/'bounded_run.py'),label,'--','/usr/bin/env','LEAN_PATH='+c['lean_path'],c['lean'],'-t','0','--root='+c['root'],'-o',str(n/(name+'.olean')),str(n/(name+'.lean'))]
raise SystemExit(subprocess.call(args,env={**os.environ,'BOOTLOOPS_MONITOR_DISABLE':'1'}))
