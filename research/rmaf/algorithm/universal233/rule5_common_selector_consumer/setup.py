#!/usr/bin/env python3
"""One-shot exact import union of completed DEVELOPMENT source roots.
The toolkit and prior pool already provide source inventories. This wrapper
checks and extends those inventories for the final classifier, never copies
raw pool audit dumps or modifies prior roots.
"""
from pathlib import Path
import datetime,hashlib,json,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[4];O=D/'build';O.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
def match(b,h):
 if sha(b)!=h:raise ValueError('BYTE_MISMATCH')
def adapted(b,m):
 s=b.decode()
 for a,z in m.items():s=re.sub(r'(?m)^import '+re.escape(a)+r'$',lambda _: 'import '+z,s)
 return s.encode()
# Independent literal plants precede candidate inventory access.
H='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad';match(b'abc',H)
controls={'clean_hash':'PASS'}
for tag,b,h in [('changed_bytes',b'abd',H),('changed_hash',b'abc','0'*64)]:
 try:match(b,h)
 except ValueError:controls[tag]='CAUGHT'
 else:raise AssertionError(tag)
assert adapted(b'import A\ndef x := 3\n',{'A':'PoolA'})==b'import PoolA\ndef x := 3\n';controls['import_only']='PASS'
assert adapted(b'import A\ndef importA := 3\n',{'A':'B'})==b'import B\ndef importA := 3\n';controls['body_untouched']='PASS'
def dedup(a,b):
 if a!=b:raise ValueError('SAME_NAME_DIFFERENT_SOURCE')
dedup(b'fixed',b'fixed');controls['duplicate_clean']='PASS'
try:dedup(b'fixed',b'corrupted')
except ValueError:controls['duplicate_corruption']='CAUGHT'
else:raise AssertionError('DUPLICATE_CORRUPTION')
if shutil.disk_usage(D).free<3*1024**3:raise RuntimeError('DISK_FLOOR_3_GIB')
P=R/'results/algorithm-universal233-ordinary-source-pool-20261015T144445575127Z';C=P/'construction.json';pool=json.loads(C.read_text())['source_modules'];assert len(pool)==306
S=R/'results/algorithm-universal233-rule5-source-orientation-replay-20261015T182316Z';cert=json.loads((S/'certificate.json').read_text());old=cert['source_entries'][:96]
manifest=R/'research/rmaf/algorithm/universal233/rule5_source_orientation_consumer/FINAL-MANIFEST-v1.json';match(manifest.read_bytes(),'a27469192042dff5e1001961ed64bac312b3c0f527ba02056263bda19a3b5fd8')
primitive=R/'research/rmaf/algorithm/universal233/rule5_common_split_source/COMMON-SPLIT-SOURCE-MANIFEST-v1.json';match(primitive.read_bytes(),'ef0d3389b3f66d46ae6c40323bed34504a1e46a882ff9a945cac5ef4c25d5523')
mapold={}
for e in old:
 n=e['module'];names=[p['module'] for p in pool if any(o['package']=='classification' and o['module']==n for o in p['origins'])]
 assert len(names)<=1,(n,names)
 mapold[n]=names[0] if names else n
entries=[]
for e in pool:
 n=e['module'];p=P/(n+'.lean');b=p.read_bytes();match(b,e['sha256']);(O/(n+'.lean')).write_bytes(b)
 if (P/(n+'.olean')).exists():shutil.copyfile(P/(n+'.olean'),O/(n+'.olean'))
 entries.append({'module':n,'source':str(p.relative_to(R)),'source_sha256':sha(b),'sha256':sha(b),'adaptations':{},'origin':'completed_pool306'})
for e in old:
 n=e['module'];z=mapold[n];p=S/(n+'.lean');b=p.read_bytes();match(b,e['sha256']);out=adapted(b,mapold);dest=O/(z+'.lean')
 if dest.exists():dedup(dest.read_bytes(),out)
 else:
  dest.write_bytes(out);entries.append({'module':z,'source':str(p.relative_to(R)),'source_sha256':sha(b),'sha256':sha(out),'adaptations':{a:v for a,v in mapold.items() if a!=v},'origin':'frozen_final_classification'})
(O/'lean-toolchain').write_bytes((S/'lean-toolchain').read_bytes())
rec={'status':'PASS_EXACT_DEVELOPMENT_SOURCE_UNION','controls':controls,'pool_construction_sha256':sha(C.read_bytes()),'orientation_manifest_sha256':sha(manifest.read_bytes()),'primitive_manifest_sha256':sha(primitive.read_bytes()),'mapping':mapold,'modules':entries,'independent_credit':0,'main_milestones':'ALL_OPEN'}
(D/'SOURCE-UNION-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],len(entries),'modules',sum((O/(e['module']+'.lean')).stat().st_size for e in entries),'source bytes')
