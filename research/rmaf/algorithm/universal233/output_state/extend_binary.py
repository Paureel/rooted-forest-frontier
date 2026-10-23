#!/usr/bin/env python3
"""One-shot frozen binary stack adapter. Import aliases identify byte-identical
restriction proof bodies already compiled from the grouped forest stack.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent;B=D/'build'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=U/'binary_cheap/BINARY-CHEAP-MANIFEST-v1.json';m=json.loads(p.read_text())
for e in m['immutable_files']:assert sha(R/e['path'])==e['sha256'],e['path']
recpath=R/m['canonical_receipt'];rec=json.loads(recpath.read_text());original=recpath.parent
stack=json.loads((D/'STACK-PINS.json').read_text());known={x['module']:x for x in stack['entries']}
new=[];runs=[]
for n in rec['positive_order']:
 p=original/(n+'.lean');data=p.read_text()
 if n in ['DepthRestriction','Embedding','Partition']:
  target={'DepthRestriction':'GroupRestriction','Embedding':'GroupEmbedding','Partition':'GroupPartition'}[n]
  normalized=data.replace('import DepthRestriction\n','import GroupRestriction\n').replace('import Embedding\n','import GroupEmbedding\n')
  assert normalized==(B/(target+'.lean')).read_text(),n
  continue
 if n in known:
  assert sha(p)==known[n]['adapted_sha256'],n
  continue
 ad={}
 for old,replacement in [('DepthRestriction','GroupRestriction'),('Embedding','GroupEmbedding'),('Partition','GroupPartition')]:
  if 'import '+old+'\n' in data:
   data=data.replace('import '+old+'\n','import '+replacement+'\n');ad[old]=replacement
 q=B/(n+'.lean');q.write_text(data)
 new.append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),adaptations=ad,adapted_sha256=sha(q)))
for row in new:
 n=row['module'];t=time.monotonic();p=subprocess.run([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(B/(n+'.lean'))],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),capture_output=True,text=True,timeout=60)
 (B/(n+'.log')).write_text(p.stdout+p.stderr);runs.append(dict(module=n,exit=p.returncode,seconds=time.monotonic()-t));assert p.returncode==0,(n,p.stdout,p.stderr)
(D/'BINARY-STACK-PINS.json').write_text(json.dumps(dict(manifest=dict(path=str((U/'binary_cheap/BINARY-CHEAP-MANIFEST-v1.json').relative_to(R)),sha256=sha(U/'binary_cheap/BINARY-CHEAP-MANIFEST-v1.json')),entries=new,runs=runs,aliases={'DepthRestriction':'GroupRestriction','Embedding':'GroupEmbedding','Partition':'GroupPartition'}),indent=2)+'\n')
print('Extended',len(new),'completed binary source modules in',round(sum(x['seconds'] for x in runs),3),'seconds')
