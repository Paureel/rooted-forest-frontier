from pathlib import Path
import datetime,hashlib,json,os,shutil
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
T=R/'research/rmaf/monitoring/next-20261016T095230Z/BINARY-PRODUCER-TARGET-v1.json';assert sha(T)=='afefb2301ac9c0ccc5dc80802eca515646f1646abbdea9a18840292b2dec2faa';t=json.loads(T.read_text());m=R/t['previous_completed']['manifest'];assert sha(m)==t['previous_completed']['sha256'];a=json.loads(m.read_text());F=R/a['canonical_receipt'];pins={x['path']:x['sha256'] for x in a['immutable_files']}
assert shutil.disk_usage(D).free>=3*1024**3
O=R/'results'/('algorithm-universal233-binary-producer-root-20261016T095230Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir();deps=[]
for p in sorted(F.glob('*.olean')):
 s=p.with_suffix('.lean')
 if not s.exists() or p.stem in ['ProviderAuditGhost','CallerAuditGhost','CallerBadConversion']:continue
 if str(s.relative_to(R)) not in pins or str(p.relative_to(R)) not in pins:continue
 files=[]
 for f in [s,p]:
  assert sha(f)==pins[str(f.relative_to(R))];q=O/f.name;assert not f.stat().st_mode&0o222;os.link(f,q)
  files.append({'original':str(f.relative_to(R)),'linked':str(q.relative_to(R)),'sha256':sha(f),'original_mode':oct(f.stat().st_mode&0o777),'original_inode':f.stat().st_ino})
 deps.append({'module':p.stem,'files':files})
assert len(deps)==497,len(deps)
(O/'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
old=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/forest_binary_caller_binding_20261016T092054Z'
for n in ['pilot.py','instrument.py']:(D/n).write_bytes((old/n).read_bytes())
rec={'root':str(O.relative_to(R)),'dependencies':deps,'pin':str(T.relative_to(R)),'pin_sha256':sha(T),'licensed_previous_manifest':str(m.relative_to(R)),'licensed_previous_sha256':sha(m),'source_pool':'Only prior sealed caller canonical pool; other licenses not merged.','dependency_rebuilds':0,'independent_credit':0}
(D/'ROOT-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print('EXACT_ROOT',len(deps),'pairs',O)
