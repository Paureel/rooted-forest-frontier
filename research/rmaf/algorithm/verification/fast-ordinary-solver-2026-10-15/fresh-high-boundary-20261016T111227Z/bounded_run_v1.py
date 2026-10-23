#!/usr/bin/env python3
"""One-shot target-local Darwin supervisor; streams only bounded gzip chunks.
Uses installed psutil for live recursive-child RSS and wait4 for kernel peak RSS.
No post-hoc acceptance of a resource failure. No producer raw export files.
"""
import argparse, gzip, hashlib, json, os, pathlib, resource, selectors, shutil, signal, subprocess, sys, time, zlib
import psutil

HERE=pathlib.Path(__file__).resolve().parent
ROOT=pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience')
p=argparse.ArgumentParser()
p.add_argument('--name',required=True)
p.add_argument('--wall',type=float,default=30)
p.add_argument('--rss-mib',type=int,default=3072)
p.add_argument('--trip-mib',type=int,default=2560)
p.add_argument('--raw-bytes',type=int,default=16*1024**2)
p.add_argument('--line-bytes',type=int,default=8*1024**2)
p.add_argument('--compressed-bytes',type=int,default=256*1024**2)
p.add_argument('--disk-floor-bytes',type=int,default=3*1024**3)
p.add_argument('--plant-missing-rss',action='store_true')
p.add_argument('command',nargs=argparse.REMAINDER)
a=p.parse_args()
cmd=a.command[1:] if a.command[:1]==['--'] else a.command
assert cmd and 0<a.wall<=59 and 0<a.trip_mib<=a.rss_mib<=3072
assert 0<a.raw_bytes<=16*1024**2 and 0<a.line_bytes<=8*1024**2 and 0<a.compressed_bytes<=256*1024**2
assert a.disk_floor_bytes>=3*1024**3 and a.name.replace('-','').replace('_','').isalnum()
out=HERE/'runs'/a.name
out.mkdir(parents=True,exist_ok=False)
start=time.monotonic()
receipt=dict(version=1,name=a.name,command=cmd,limits=vars(a).copy(),started=False,
             status='REFUSED',reason=None,observed_pids={},sample_count=0,
             peak_aggregate_rss=0,kernel_peak_rss=0,raw_seen=0,raw_retained=0,
             compressed_bytes=0,max_line_seen=0,chunks=[],elapsed_seconds=0)
receipt['limits'].pop('command')
proc=None
failure=None
returncode=None
kernel_usage=None
current=None
compressor=None
chunk_raw=0
chunk_hash=None
chunk_packed_hash=None
chunk_packed=0
chunk_index=0
line_length=0

def reject(reason):
    global failure
    if failure is None: failure=reason

def emit_packed(data):
    global chunk_packed
    if receipt['compressed_bytes']+len(data)>a.compressed_bytes:
        reject('COMPRESSED_LIMIT')
        return
    current.write(data)
    chunk_packed_hash.update(data)
    chunk_packed+=len(data)
    receipt['compressed_bytes']+=len(data)

def open_chunk():
    global current,compressor,chunk_raw,chunk_hash,chunk_packed_hash,chunk_packed
    current=(out/f'output-{chunk_index:03}.log.gz').open('xb')
    compressor=zlib.compressobj(6,zlib.DEFLATED,31)
    chunk_raw=0
    chunk_packed=0
    chunk_hash=hashlib.sha256()
    chunk_packed_hash=hashlib.sha256()

def close_chunk():
    global current,chunk_index
    if current is None: return
    emit_packed(compressor.flush())
    current.close()
    receipt['chunks'].append(dict(path=current.name,raw_bytes=chunk_raw,raw_sha256=chunk_hash.hexdigest(),
                                  compressed_bytes=chunk_packed,compressed_sha256=chunk_packed_hash.hexdigest(),
                                  complete=failure is None))
    current=None
    chunk_index+=1

def consume(data):
    global line_length,chunk_raw
    receipt['raw_seen']+=len(data)
    if receipt['raw_seen']>a.raw_bytes:
        reject('RAW_LIMIT')
        return
    pieces=data.split(b'\n')
    for i,piece in enumerate(pieces):
        line_length+=len(piece)
        receipt['max_line_seen']=max(receipt['max_line_seen'],line_length)
        if line_length>a.line_bytes:
            reject('LINE_LIMIT')
            return
        if i+1<len(pieces): line_length=0
    while data and failure is None:
        if current is None: open_chunk()
        take=min(len(data),4*1024**2-chunk_raw)
        block,data=data[:take],data[take:]
        chunk_hash.update(block)
        chunk_raw+=take
        receipt['raw_retained']+=take
        emit_packed(compressor.compress(block))
        if chunk_raw==4*1024**2: close_chunk()

def child_setup():
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    resource.setrlimit(resource.RLIMIT_FSIZE,(16*1024**2,16*1024**2))

def kill_all():
    if proc is None: return
    try: os.killpg(proc.pid,signal.SIGKILL)
    except ProcessLookupError: pass
    for pid in receipt['observed_pids']:
        try: psutil.Process(int(pid)).kill()
        except (psutil.NoSuchProcess,ProcessLookupError): pass

try:
    if shutil.disk_usage(HERE).free<a.disk_floor_bytes:
        reject('DISK_FLOOR')
    else:
        env=os.environ.copy()
        env['LEAN_PATH']=str(HERE)+':'+str(ROOT/'results/algorithm-universal233-fast-ordinary-recursion-replay-20261015T205325296780Z')
        proc=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env=env,cwd=HERE,
                              start_new_session=True,preexec_fn=child_setup)
        receipt['started']=True
        root_process=psutil.Process(proc.pid)
        tracked={proc.pid:root_process}
        selector=selectors.DefaultSelector()
        os.set_blocking(proc.stdout.fileno(),False)
        selector.register(proc.stdout,selectors.EVENT_READ)
        pipe_open=True
        reaped=False
        while not reaped or pipe_open:
            if time.monotonic()-start>a.wall: reject('WALL_LIMIT')
            if shutil.disk_usage(HERE).free<a.disk_floor_bytes: reject('DISK_FLOOR')
            if failure is not None: kill_all()
            if not reaped:
                if a.plant_missing_rss:
                    reject('RSS_MEASUREMENT_UNAVAILABLE')
                else:
                    try:
                        for child in root_process.children(recursive=True): tracked[child.pid]=child
                    except psutil.NoSuchProcess: pass
                    except psutil.AccessDenied: reject('CHILD_ENUMERATION_UNAVAILABLE')
                    aggregate=0
                    for pid,process in list(tracked.items()):
                        try:
                            rss=process.memory_info().rss
                            aggregate+=rss
                            previous=receipt['observed_pids'].get(str(pid),0)
                            receipt['observed_pids'][str(pid)]=max(previous,rss)
                        except psutil.NoSuchProcess: pass
                        except psutil.AccessDenied: reject('RSS_MEASUREMENT_UNAVAILABLE')
                    receipt['sample_count']+=1
                    receipt['peak_aggregate_rss']=max(receipt['peak_aggregate_rss'],aggregate)
                    if aggregate>=a.trip_mib*1024**2: reject('RSS_TRIP_LIMIT')
                    if aggregate>a.rss_mib*1024**2: reject('RSS_HARD_LIMIT')
                try:
                    waited,status,usage=os.wait4(proc.pid,os.WNOHANG)
                    if waited:
                        reaped=True
                        returncode=os.waitstatus_to_exitcode(status)
                        proc.returncode=returncode
                        kernel_usage=usage
                except ChildProcessError:
                    reject('WAIT4_PEAK_UNAVAILABLE')
                    reaped=True
            for key,_ in selector.select(0.005):
                data=os.read(key.fileobj.fileno(),65536)
                if data:
                    if failure is None: consume(data)
                else:
                    selector.unregister(key.fileobj)
                    pipe_open=False
            if reaped and pipe_open and time.monotonic()-start>a.wall: kill_all()
        selector.close()
        if kernel_usage is not None:
            peak=kernel_usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024)
            receipt['kernel_peak_rss']=peak
            if peak>a.rss_mib*1024**2: reject('KERNEL_RSS_HARD_LIMIT')
        else: reject('WAIT4_PEAK_UNAVAILABLE')
        if not receipt['sample_count'] or not receipt['observed_pids']: reject('RSS_MEASUREMENT_UNAVAILABLE')
        for pid,process in tracked.items():
            if pid==proc.pid: continue
            try:
                if process.is_running() and process.status()!=psutil.STATUS_ZOMBIE:
                    reject('CHILD_REMAINED_AFTER_PRODUCER')
            except psutil.NoSuchProcess: pass
        if failure is not None: kill_all()
    close_chunk()
    if failure is None:
        for chunk in receipt['chunks']:
            packed=pathlib.Path(chunk['path']).read_bytes()
            restored=gzip.decompress(packed)
            if len(restored)>4*1024**2 or len(restored)!=chunk['raw_bytes'] or hashlib.sha256(restored).hexdigest()!=chunk['raw_sha256']:
                reject('CHUNK_INTEGRITY')
        if returncode!=0: reject('PRODUCER_FAILURE')
except BaseException as exc:
    reject('SUPERVISOR_EXCEPTION:'+type(exc).__name__+':'+str(exc))
    kill_all()
    if current is not None:
        try: close_chunk()
        except BaseException: current.close()
finally:
    receipt['reason']=failure
    receipt['returncode']=returncode
    receipt['status']='ACCEPT' if failure is None else 'REFUSED'
    receipt['elapsed_seconds']=time.monotonic()-start
    receipt['disk_free_bytes']=shutil.disk_usage(HERE).free
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['name','status','reason','returncode','elapsed_seconds','peak_aggregate_rss','kernel_peak_rss','raw_seen','compressed_bytes','observed_pids']}))
raise SystemExit(0 if failure is None else 75)
