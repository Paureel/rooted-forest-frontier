#!/usr/bin/env python3
"""One-shot v9 adapter of the prior license-gated reader, not an author program.
Only the release binding/contact directory changes; explicit controls exercise
the same license/hash/size/line checks before new scientific source contact.
"""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,shutil
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');HERE=Path(__file__).resolve().parent
RELEASE=ROOT/'research/rmaf/algorithm/verification/runtime233-2026-10-15/ROOT-RELEASE-v9.json'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
def decode(raw,expected,rawcap=64*1024**2,linecap=16*1024**2,compressed=False):
    if expected is None:raise ValueError('unlicensed')
    if sha(raw)!=expected:raise ValueError('hash drift')
    if len(raw)>rawcap:raise ValueError('rawcap')
    data=gzip.decompress(raw) if compressed else raw
    if len(data)>rawcap:raise ValueError('expandedcap')
    lines=data.decode().splitlines()
    if max(map(len,lines),default=0)>linecap:raise ValueError('linecap')
    return data,lines
a=argparse.ArgumentParser();a.add_argument('--selftest',action='store_true');a.add_argument('--file');a.add_argument('--start',type=int,default=1);a.add_argument('--end',type=int,default=200);a.add_argument('--keys',action='store_true');a.add_argument('--paths');o=a.parse_args()
if o.selftest:
    f=json.loads((HERE/'READER-CONTROLS-v9.json').read_text());out=[];raw=f['known_text'].encode();expected=f['known_sha256']
    assert decode(raw,expected)[1]==f['expected_lines'];out.append({'case':'known abc','pass':True})
    for name,rr,ee,rc,lc in [('changed',f['changed_text'].encode(),expected,64,16),('unlicensed',raw,None,64,16),('rawcap',raw,expected,2,16),('linecap',raw,expected,64,2)]:
        try:decode(rr,ee,rc,lc)
        except ValueError:out.append({'case':name,'pass':True});continue
        raise AssertionError('missed '+name)
    assert len(out)==f['expected_good']+f['expected_rejected']
    (HERE/'READER-CONTROL-RESULTS-v9.json').write_text(json.dumps(out,indent=2)+'\n');print('Reader adapter:1 known answer,4 rejected corruptions.')
else:
    if not (HERE/'READER-CONTROL-RESULTS-v9.json').exists():raise RuntimeError('controls first')
    raw=RELEASE.read_bytes();assert sha(raw)=='775fc4dd1ca858d6cd0e9796f08aa959b8427d29f3737770d96687e5d4eb783f'
    release=json.loads(raw);idx={x['path']:x['sha256'] for x in release['licensed_immutable_files']};idx.update({x['manifest']:x['sha256'] for x in release['licensed_packages']})
    if o.paths:
        for name in idx:
            if o.paths in name:print(name)
    else:
        if shutil.disk_usage(HERE).free<3*1024**3:raise RuntimeError('diskfloor')
        p=ROOT/str(o.file)
        if o.file not in idx:raise ValueError('UNLICENSED '+str(o.file))
        if p.stat().st_size>64*1024**2:raise ValueError('rawcap')
        raw=p.read_bytes();data,lines=decode(raw,idx[o.file],compressed=o.file.endswith('.gz'))
        event={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':o.file,'sha256':sha(raw),'bytes':len(raw),'requested_lines':[o.start,o.end],'keys':o.keys,'scope':'v9 postcontact source reading; zero new blind credit'}
        with (HERE/'CONTACT-v9.jsonl').open('a') as h:h.write(json.dumps(event,sort_keys=True)+'\n')
        if o.keys:
            obj=json.loads(data)
            if not isinstance(obj,dict):raise ValueError('keys mode requires object')
            print(json.dumps({k:(v if len(str(v))<5000 else {'type':type(v).__name__,'length':len(v)}) for k,v in obj.items()},indent=2))
        else:
            print(o.file+' SHA256 '+sha(raw)+' total_lines '+str(len(lines)))
            for i in range(o.start-1,min(o.end,len(lines))):print(str(i+1)+': '+lines[i])
