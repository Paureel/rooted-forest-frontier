from pathlib import Path
import datetime,importlib.util,json,os,sys
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/json.loads((D/'BUILD-v1.json').read_text())['directory'];O=B/'supervisor-controls-v4';O.mkdir()
s=importlib.util.spec_from_file_location('own_measured_supervisor',D/'supervisor_v4.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
cases=[('positive','print(2)',None,0,2),('false','raise SystemExit(7)',None,7,2),('rss','import time;x=bytearray(96*1024**2);time.sleep(1)','rss',0,2),('raw','import sys;[sys.stdout.write("x"*32767+"\\n") for _ in range(80)]','raw',0,2),('line','print("x"*700000)','line',0,2),('disk','import time;time.sleep(.2)','disk',0,2),('time','import time;time.sleep(2)','time',0,.1)]
cases.append(('nested_peak',"import subprocess,sys;p=subprocess.Popen([sys.executable,'-c','import time;x=bytearray(96*1024**2);time.sleep(.1)']);p.wait()",None,0,2))
rows=[]
for label,source,plant,want,seconds in cases:
 p=O/(label+'.py');p.write_text(source+'\n');row,_=m.run([sys.executable,str(p)],R,os.environ.copy(),O,label,seconds=seconds,want=want,plant=plant);rows.append(row)
assert rows[-1]['wait4_exact_peak_RSS_bytes']>=96*(1<<20),('DESCENDANT_PEAK_NOT_ACCUMULATED',rows[-1])
result=dict(status='PASS_MEASURED_SUPERVISOR_POSITIVE_EXIT_RSS_RAW_LINE_DISK_TIME_CONTROLS',rows=rows,independent_credit=0);(O/'controls.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'])
