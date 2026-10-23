#!/usr/bin/env python3
"""One-campaign supervisor: bounded compressed evidence, no shared dashboard writes.

Use: BOOTLOOPS_MONITOR_DISABLE=1 ./bootloops-python <this> LABEL -- COMMAND...
Output means process evidence only, never mathematical acceptance. Each process has
a hard 60s bound, 16MiB raw output cap, 8MiB line cap; measured RSS<=3072MiB and 3GiB free-space floor.
"""
import resource, psutil
import datetime, gzip, hashlib, json, os, pathlib, selectors, signal, subprocess, sys, time

HERE = pathlib.Path(__file__).resolve().parent
CAP, FLOOR, RAW, LINE = 256*1024**2, 3*1024**3, 16*1024**2, 8*1024**2

def resources(enforce=True):
    free = os.statvfs(HERE).f_bavail * os.statvfs(HERE).f_frsize
    compressed = sum(p.stat().st_size for p in HERE.rglob('*.gz'))
    if enforce and free < FLOOR: raise RuntimeError('free-space floor')
    if enforce and compressed >= CAP: raise RuntimeError('compressed-output cap')
    return free, compressed

def main():
    label, args = sys.argv[1], sys.argv[2:]
    if args[0] == '--': args = args[1:]
    if not label.replace('-', '').replace('_', '').isalnum(): raise ValueError('label')
    out = HERE/'evidence'; out.mkdir(exist_ok=True)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    stem = out/f'{stamp}-{label}'
    start_free, start_compressed = resources(enforce=False)
    # Test overrides can only tighten hard bounds. 59s leaves termination margin.
    raw_cap=min(RAW,int(os.getenv('SOL_TEST_RAW_CAP',str(RAW))))
    line_cap=min(LINE,int(os.getenv('SOL_TEST_LINE_CAP',str(LINE))))
    stage=os.getenv('SOL_RUN_STAGE','pilot')
    if stage not in ('pilot','audit'):raise ValueError('stage')
    ceiling=30.0 if stage=='pilot' else 59.0
    time_cap=min(ceiling,float(os.getenv('SOL_TEST_TIME_CAP',str(ceiling))))
    rss_cap=min(3072*1024**2,int(os.getenv('SOL_TEST_RSS_CAP',str(3072*1024**2))))
    peak_rss=0;peak_os_rss=0
    def sample_rss():
        if proc is None:return 0
        try:
            root=psutil.Process(proc.pid);family=[root]+root.children(recursive=True)
        except psutil.NoSuchProcess:return 0
        total=0
        for member in family:
            try:total+=member.memory_info().rss
            except psutil.NoSuchProcess:pass
        return total
    if min(raw_cap,line_cap,time_cap)<=0:raise ValueError('positive tightened caps')
    begun = time.monotonic(); count = 0; retained=0; current_line = 0; shard_bytes = 0; shard = 0
    paths = []; reason = None
    proc=None
    sel = selectors.DefaultSelector()
    log = None
    try:
        resources()
        proc = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                start_new_session=True, env={**os.environ, 'BOOTLOOPS_MONITOR_DISABLE':'1'})
        sel.register(proc.stdout, selectors.EVENT_READ)
        while sel.get_map():
            if time.monotonic()-begun > time_cap: raise RuntimeError('time cap')
            peak_rss=max(peak_rss,sample_rss())
            if peak_rss>rss_cap:raise RuntimeError('peak RSS cap')
            resources()
            for key, _ in sel.select(min(0.01,max(0.001,time_cap-(time.monotonic()-begun)))):
                chunk = os.read(key.fileobj.fileno(), 65536)
                if not chunk:
                    sel.unregister(key.fileobj); continue
                count += len(chunk)
                keep=chunk[:max(0,raw_cap-retained)]
                # Retain a bounded prefix even when the process violates a cap.
                accepted=[];line_violation=False;parts=keep.split(b'\n')
                for i,part in enumerate(parts):
                    allowance=max(0,line_cap-current_line)
                    accepted.append(part[:allowance]);current_line+=min(len(part),allowance)
                    if len(part)>allowance:
                        line_violation=True;break
                    if i<len(parts)-1:accepted.append(b'\n');current_line=0
                keep=b''.join(accepted)
                if log is None or shard_bytes+len(keep)>4*1024**2:
                    if log: log.close()
                    p=pathlib.Path(str(stem)+f'-{shard:03d}.log.gz'); paths.append(p)
                    log=gzip.open(p,'wb'); shard+=1; shard_bytes=0
                log.write(keep);log.flush();shard_bytes+=len(keep);retained+=len(keep)
                if count > raw_cap: raise RuntimeError('raw cap')
                if line_violation: raise RuntimeError('line cap')
        remaining=max(0.001,time_cap-(time.monotonic()-begun))
        proc.wait(timeout=remaining)
        peak_os_rss=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        if sys.platform!='darwin':peak_os_rss*=1024
        if max(peak_rss,peak_os_rss)>rss_cap:raise RuntimeError('peak RSS cap')
    except Exception as exc:
        reason=str(exc)
        if proc is not None:
            try:os.killpg(proc.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            proc.wait(timeout=0.5)
    finally:
        if log: log.close()
        sel.close()
    # Resource refusal itself must be preserved, including a mid-run floor stop.
    free, compressed=resources(enforce=False)
    record={'label':label,'utc':stamp,'command':args,'seconds':time.monotonic()-begun,
            'returncode':None if proc is None else proc.returncode,'stop_reason':reason,'raw_bytes':count,
            'retained_raw_bytes':retained,'peak_sampled_family_rss_bytes':peak_rss,'peak_os_child_rss_bytes':peak_os_rss,'stage':stage,'effective_caps':{'raw':raw_cap,'line':line_cap,'seconds':time_cap,'rss_bytes':rss_cap,'shard_raw_bytes':4*1024**2},
            'free_before':start_free,'free_after':free,'compressed_before':start_compressed,
            'compressed_after':compressed,'shards':[{'path':str(p.relative_to(HERE)),
            'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths]}
    pathlib.Path(str(stem)+'.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,sort_keys=True))
    return 0 if proc is not None and proc.returncode==0 and reason is None else 1

if __name__=='__main__': sys.exit(main())
