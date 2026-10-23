#!/usr/bin/env python3
"""One-shot license-gated source reader; no author program is executed.
Postcontact utility, zero blind credit; logs exact file contacts before output.
"""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,shutil
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
HERE=Path(__file__).resolve().parent
RELEASE=ROOT/'research/rmaf/algorithm/verification/runtime233-2026-10-15/ROOT-RELEASE-v1.json'
a=argparse.ArgumentParser();a.add_argument('--file');a.add_argument('--start',type=int,default=1);a.add_argument('--end',type=int,default=240);a.add_argument('--keys',action='store_true');a.add_argument('--paths');opts=a.parse_args()
r=json.loads(RELEASE.read_text());license={x['path']:x['sha256'] for x in r['licensed_immutable_files']};license.update({x['manifest']:x['sha256'] for x in r['licensed_packages']})
if opts.paths:
    for name in license:
        if opts.paths in name: print(name)
else:
    name=opts.file
    if name not in license: raise RuntimeError('UNLICENSED '+str(name))
    if shutil.disk_usage(HERE).free<3*1024**3: raise RuntimeError('diskfloor')
    p=ROOT/name
    if p.stat().st_size>64*1024**2: raise RuntimeError('rawcap')
    raw=p.read_bytes();digest=hashlib.sha256(raw).hexdigest()
    if digest!=license[name]:raise RuntimeError('source hash drift')
    data=gzip.decompress(raw) if name.endswith('.gz') else raw
    if len(data)>64*1024**2:raise RuntimeError('decompressed cap')
    lines=data.decode().splitlines()
    if max(map(len,lines),default=0)>16*1024**2:raise RuntimeError('linecap')
    event={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'event':'RELEASED_SCIENTIFIC_FILE_READ','path':name,'sha256':digest,'bytes':len(raw),'requested_lines':[opts.start,opts.end],'json_key_summary':opts.keys,'postcontact_adaptation':True,'new_blind_credit':0}
    with (HERE/'CONTACT-v1.jsonl').open('a') as f:f.write(json.dumps(event,sort_keys=True)+'\n')
    if opts.keys:
        obj=json.loads(data)
        print(json.dumps({k:(v if not isinstance(v,(dict,list)) or len(str(v))<3000 else {'type':type(v).__name__,'length':len(v)}) for k,v in obj.items()},indent=2))
    else:
        print(name+' SHA256 '+digest+' total_lines '+str(len(lines)))
        for i in range(opts.start-1,min(opts.end,len(lines))): print(str(i+1)+': '+lines[i])
