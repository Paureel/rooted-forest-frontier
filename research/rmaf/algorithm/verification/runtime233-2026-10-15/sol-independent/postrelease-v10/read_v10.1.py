"""License-gated streaming adapter. Whole-file SHA in <=4MiB chunks;
selected UTF8 lines <=8MiB each/output <=16MiB. No author program executed."""
from pathlib import Path
import argparse,hashlib,json,datetime,shutil,io
R=Path('/Users/paurel/Documents/ChatGPT/bootscience');P=Path(__file__).resolve().parent
CHUNK=4*1024**2;LINE=8*1024**2;OUT=16*1024**2
sha=lambda raw:hashlib.sha256(raw).hexdigest()
def streamed(f,expected,start,end,linecap=LINE,outcap=OUT,chunk=CHUNK):
 if expected is None:raise ValueError('unlicensed')
 h=hashlib.sha256();total=0
 while b:=f.read(chunk):h.update(b);total+=len(b)
 if h.hexdigest()!=expected:raise ValueError('hash drift')
 f.seek(0);selected=[];size=0;n=0
 while True:
  raw=f.readline(linecap+1)
  if not raw:break
  if len(raw)>linecap:raise ValueError('linecap')
  n+=1
  if start<=n<=end:
   size+=len(raw)
   if size>outcap:raise ValueError('outputcap')
   selected.append((n,raw.decode().rstrip('\n')))
 return total,n,selected
ap=argparse.ArgumentParser();ap.add_argument('--selftest',action='store_true');ap.add_argument('--file');ap.add_argument('--start',type=int,default=1);ap.add_argument('--end',type=int,default=150);o=ap.parse_args()
if o.selftest:
 fixed='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
 assert streamed(io.BytesIO(b'abc'),fixed,1,1,chunk=1)==(3,1,[(1,'abc')])
 out=['known abc under1byte chunks']
 for name,raw,pin,lc,oc in [('changed',b'abd',fixed,8,8),('unlicensed',b'abc',None,8,8),('linecap',b'abc',fixed,2,8),('outputcap',b'abc',fixed,8,2)]:
  try:streamed(io.BytesIO(raw),pin,1,1,lc,oc,1)
  except ValueError:out.append(name+' rejected');continue
  raise AssertionError(name)
 (P/'READER-STREAM-CONTROL-RESULTS-v10.1.json').write_text(json.dumps(dict(status='KNOWN_AND4HOSTILES_MET',cases=out,known_pin=fixed,new_blind_credit=0),indent=2)+'\n');print(out)
else:
 assert (P/'READER-STREAM-CONTROL-RESULTS-v10.1.json').exists()
 assert shutil.disk_usage(P).free>=3*1024**3
 rel='research/rmaf/algorithm/verification/runtime233-2026-10-15/ROOT-RELEASE-v10.json';raw=(R/rel).read_bytes();assert sha(raw)=='e132799b88c5508bd1998a54c4f95e504da3f39a5685c2a6800feb97bd03093b';r=json.loads(raw);idx={x['path']:x['sha256'] for x in r['licensed_immutable_files']};idx.update({x['manifest']:x['sha256'] for x in r['licensed_packages']});expected=idx.get(o.file)
 if expected is None:raise ValueError('UNLICENSED '+str(o.file))
 with (R/o.file).open('rb') as f:total,n,selected=streamed(f,expected,o.start,o.end)
 e=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=o.file,sha256=expected,bytes=total,total_lines=n,requested_lines=[o.start,o.end],stream_chunk=CHUNK,line_cap=LINE,output_cap=OUT,scope='Exact v10 postcontact body reading;0newblind')
 with (P/'CONTACT-v10.jsonl').open('a') as f:f.write(json.dumps(e)+'\n')
 print(o.file+' SHA256 '+expected+' total_lines '+str(n))
 for i,s in selected:print(str(i)+': '+s)
