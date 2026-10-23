#!/usr/bin/env python3
"""One-shot campaign supervisor, intentionally local to this proof arm.

The toolkit's Turnstile is Linux admission control, not a Darwin RSS/output
limiter; BALLER is a numerical instrument. Neither supplies these controls.
This bounded wrapper records wall/RSS/output violations and fails closed.
Limits can only be tightened except disk-floor, which can only be raised.
"""
import argparse, gzip, json, os, resource, selectors, shutil, signal
import subprocess, sys, time
from pathlib import Path
import psutil

MiB = 1024**2
p = argparse.ArgumentParser()
p.add_argument('--name', required=True)
p.add_argument('--wall', type=float, default=30)
p.add_argument('--rss', type=int, default=3072*MiB)
p.add_argument('--raw', type=int, default=16*MiB)
p.add_argument('--line', type=int, default=8*MiB)
p.add_argument('--compressed', type=int, default=256*MiB)
p.add_argument('--floor', type=int, default=3*1024**3)
p.add_argument('cmd', nargs=argparse.REMAINDER)
a=p.parse_args()
assert 0 < a.wall <= 59 and 0 < a.rss <= 3072*MiB
assert 0 < a.raw <= 16*MiB and 0 < a.line <= 8*MiB
assert 0 < a.compressed <= 256*MiB and a.floor >= 3*1024**3
cmd=a.cmd[1:] if a.cmd[:1]==['--'] else a.cmd
assert cmd
out=Path(__file__).resolve().parent/'runs'/a.name
out.mkdir(parents=True,exist_ok=False)
start=time.monotonic(); peak=0; total=0; lines={}; violation=None
free=shutil.disk_usage(out).free
receipt={'command':cmd,'limits':vars(a),'started_unix':time.time(),
         'initial_free_bytes':free,'measurement':'psutil recursive RSS samples plus wait4 direct-child ru_maxrss'}
child=None; rc=None; observations=0
try:
    if free < a.floor:
        violation='disk_floor_before_spawn'
    else:
        child=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                               start_new_session=True)
        proc=psutil.Process(child.pid); sel=selectors.DefaultSelector()
        for n,s in [('stdout',child.stdout),('stderr',child.stderr)]:
            os.set_blocking(s.fileno(),False); sel.register(s,selectors.EVENT_READ,n)
            lines[n]=0
        streams={n:gzip.open(out/(n+'.gz'),'wb',compresslevel=6) for n in lines}
        done=False
        while not done or sel.get_map():
            elapsed=time.monotonic()-start
            if elapsed > a.wall and violation is None: violation='wall'
            if shutil.disk_usage(out).free < a.floor and violation is None: violation='disk_floor'
            if not done:
                try:
                    group=[proc]+proc.children(recursive=True)
                    rss=0
                    for q in group:
                        try: rss+=q.memory_info().rss
                        except psutil.NoSuchProcess: pass
                    peak=max(peak,rss); observations+=1
                    if rss>a.rss and violation is None: violation='rss_sample'
                except psutil.NoSuchProcess: pass
                except Exception as e:
                    if violation is None: violation='rss_measurement:'+repr(e)
                pid,status,ru=os.wait4(child.pid,os.WNOHANG)
                if pid:
                    rc=os.waitstatus_to_exitcode(status); child.returncode=rc; done=True
                    rupeak=int(ru.ru_maxrss)*(1 if sys.platform=='darwin' else 1024)
                    peak=max(peak,rupeak)
                    if peak>a.rss and violation is None: violation='rss_peak'
            if violation and not done:
                try: os.killpg(child.pid,signal.SIGKILL)
                except ProcessLookupError: pass
            for key,_ in sel.select(.01):
                chunk=os.read(key.fileobj.fileno(),65536)
                if not chunk: sel.unregister(key.fileobj); key.fileobj.close(); continue
                total+=len(chunk)
                if total>a.raw and violation is None: violation='raw_output'
                segments=chunk.split(b'\n')
                linepeak=max([lines[key.data]+len(segments[0])]+[len(x) for x in segments[1:]])
                lines[key.data]=(lines[key.data]+len(chunk)) if len(segments)==1 else len(segments[-1])
                if linepeak>a.line and violation is None: violation='line_output'
                if total<=a.raw and linepeak<=a.line:
                    streams[key.data].write(chunk); streams[key.data].flush()
                comp=sum(f.stat().st_size for f in out.glob('*.gz'))
                global_comp=sum(f.stat().st_size for f in out.parent.rglob('*.gz'))
                if comp>a.compressed and violation is None: violation='compressed_output'
                if global_comp>256*MiB and violation is None: violation='compressed_output_total'
        for f in streams.values(): f.close()
        comp=sum(f.stat().st_size for f in out.glob('*.gz'))
        if comp>a.compressed and violation is None: violation='compressed_output_final'
        if observations==0 and violation is None: violation='no_rss_observations'
except BaseException as e:
    if child and child.returncode is None:
        try: os.killpg(child.pid,signal.SIGKILL)
        except ProcessLookupError: pass
    violation=violation or 'supervisor_exception:'+repr(e)
finally:
    receipt.update(exit_code=rc,violation=violation,wall_seconds=time.monotonic()-start,
                   peak_rss_bytes=peak,raw_bytes=total,rss_observations=observations,
                   compressed_bytes=sum(f.stat().st_size for f in out.glob('*.gz')))
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['exit_code','violation','wall_seconds','peak_rss_bytes','raw_bytes','rss_observations']}))
sys.exit(125 if violation else (rc or 0))
