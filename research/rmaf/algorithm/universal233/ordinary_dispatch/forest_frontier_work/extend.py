from pathlib import Path
import hashlib,json,shutil
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();s=json.loads((D/'ROOT-v1.json').read_text());O=R/s['root'];m=json.loads((R/s['manifests'][0]['path']).read_text());assert sha(R/s['manifests'][0]['path'])==s['manifests'][0]['sha256'];pins={e['path']:e['sha256'] for e in m['immutable_files']};S=R/m['canonical_receipt'];n='ForestTrace';row={'module':n,'files':[],'imports':['ForestWorkBound']}
for ext in ['.lean','.olean']:
 p=S/(n+ext);q=O/p.name;h=pins[str(p.relative_to(R))];assert sha(p)==h and not q.exists();shutil.copyfile(p,q);q.chmod(0o444);assert sha(q)==h
 row['files'].append({'original':str(p.relative_to(R)),'sha256':h,'original_mode':oct(p.stat().st_mode&0o777),'linked':str(q.relative_to(R)),'inode':q.stat().st_ino,'device':q.stat().st_dev,'snapshot_kind':'EXACT_READONLY_COPY_FROM_WRITABLE_MODE_FROZEN_BYTES'})
s['dependencies'].append(row);s['seeds'].append(n);s['root_v1_sha256']=sha(D/'ROOT-v1.json');(D/'ROOT-v2.json').write_text(json.dumps(s,indent=2)+'\n');print('ADDED_EXACT_FOREST_TRACE',len(s['dependencies']))
