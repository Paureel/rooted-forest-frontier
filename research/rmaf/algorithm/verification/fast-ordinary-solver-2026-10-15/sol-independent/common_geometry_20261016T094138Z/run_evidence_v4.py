import pathlib,json,sys,subprocess,os
n=pathlib.Path(__file__).resolve().parent
c=json.loads((n/'EVIDENCE-RUN-CONFIG-v4.json').read_text())
mode=sys.argv[1];assert mode in ['body','closure']
a=[sys.executable,str(n/'bounded_run.py'),'geometry-own-'+mode+'-v4','--']+c[mode+'_command']
raise SystemExit(subprocess.call(a,env={**os.environ,'BOOTLOOPS_MONITOR_DISABLE':'1'}))
