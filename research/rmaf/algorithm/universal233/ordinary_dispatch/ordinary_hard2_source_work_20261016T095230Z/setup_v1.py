from pathlib import Path
import datetime,hashlib,json,os,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
T=R/'research/rmaf/monitoring/next-20261016T095230Z/MAIN-HARD2-TARGET-v1.json';assert sha(T)=='6872bfde16cc1fad8c9d7208a63237aa12b4bfa11e8f6833f46f94de0f75ba5d';t=json.loads(T.read_text());e=t['previous_completed'];p=R/e['manifest'];assert sha(p)==e['sha256'];m=json.loads(p.read_text())
for f in m['immutable_files']:assert sha(R/f['path'])==f['sha256']
P=R/m['canonical_build'];assert shutil.disk_usage(R).free>=3*(1<<30)
B=R/'results'/('algorithm-universal233-hard2-source-20261016T095230Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));B.mkdir();sources=[]
for p in sorted(P.glob('*.lean')):
 o=P/(p.stem+'.olean')
 if not o.exists():continue
 for s in [p,o]:assert not s.stat().st_mode&0o222;os.link(s,B/s.name)
 sources.append(dict(module=p.stem,source=str(p.relative_to(R)),source_sha256=sha(p),olean=str(o.relative_to(R)),olean_sha256=sha(o)))
shutil.copyfile(P/'lean-toolchain',B/'lean-toolchain')
s=dict(status='PASS_EXACT_LICENSED_CONSUMER_SEED_COMPATIBILITY_AUDIT_PENDING',target_sha256=sha(T),previous_manifest=e,sources=sources,object_identity_differences=[],source_conflicts=[],independent_acceptance=False,all_main_milestones='OPEN')
(B/'SEED.json').write_text(json.dumps(s,indent=2)+'\n');(D/'BUILD-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),seed_sha256=sha(B/'SEED.json')),indent=2)+'\n');print(B,len(sources))
