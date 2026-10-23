#!/usr/bin/env python3
"""One-shot exact scoped review seal; preserves prior READY and author freezes."""
import datetime,hashlib,json,os,pathlib,shutil
H=pathlib.Path(__file__).resolve().parent; ROOT=H.parents[5]; REVIEW=H.parent; READY=REVIEW/'sol-frozen-ready-v1'; DEST=REVIEW/'sol-frozen-review-v1'
if DEST.exists():raise SystemExit('refuse overwrite of immutable review seal')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
readyhash='25673f06bb120f25235aba32781acd07654fa44d98e258f96eba74a8fcbfce78';assert sha(READY/'READY-MANIFEST-v1.json')==readyhash
rm=json.loads((READY/'READY-MANIFEST-v1.json').read_text());assert len(rm['files'])==264
for r in rm['files']:assert sha(READY/r['path'])==r['sha256']
release=json.loads((H/'release-integrity-v1.json').read_text());total=0
for m in release['manifests']:
 p=ROOT/m['manifest'];assert sha(p)==m['sha256'];data=json.loads(p.read_text());assert len(data['immutable_files'])==m['fileCount'];total+=len(data['immutable_files'])
 for r in data['immutable_files']:assert sha(ROOT/r['path'])==r['sha256']
assert total==180
build=json.loads((H/'build-v1.json').read_text());assert build['completedModules']==25 and build['scientificOleansCopied'] is False
for r in build['records']:
 assert sha(H/'isolated'/(r['module']+'.lean'))==r['sourceSHA256'];assert sha(H/'isolated'/(r['module']+'.olean'))==r['oleanSHA256']
manual=['CompletionConsumers','Consumers','StateExpand','Replacement','Reverse','Forward','Singleton','Endpoint','StateContract','Contraction','BlockPartition','Removal','QuotientGeometry','QuotientTopology','Expansion','CherryGraph','StateEmbedding','CherryTopology','GraphControls','Controls','LeafClear']
contacts={'releasedSources':[{'module':m['module'],'sourcePath':m['path'],'sha256':m['sha256'],'contact':'exact bytes, import headers, literal defs/abbrevs, full compiled declaration/types/axioms audit'+('; full body manually read' if m['module'] in manual else '; State public definitions/RMAF definition ranges previously read; other source body only compiled/compared')} for m in release['formalModules']], 'pinnedOriginalBridgeDependencies':[{'path':p,'sha256':sha(ROOT/p),'contact':'byte comparison to released renamed/import-adapted source only'} for p in ['research/rmaf/algorithm/universal233/restriction_bridge/Restriction.lean','research/rmaf/algorithm/universal233/restriction_bridge/Embedding.lean','research/rmaf/algorithm/universal233/restriction_bridge/Partition.lean']], 'canonicalReceipts':['results/algorithm-universal233-state-20261015T094847Z/certificate.json','results/algorithm-universal233-state-cherry-20261015T101755Z/certificate.json'],'receiptUse':'manifests/structured source pins and import adapters; initial large print truncated; author numerical counts/controls not used as independent expected values', 'additionalAPIs':['installed Lean/Util/Path.lean findOLean signature lookup; frozen preparation Environment/CollectAxioms/Eqns APIs'], 'additionalSkills':[{'path':'.agents/skills/'+s+'/SKILL.md','sha256':sha(ROOT/'.agents/skills'/s/'SKILL.md')} for s in ['prose-lint','referee-sim']], 'authorAuditReplayImplementationRead':False,'otherReviewerCodeRead':False,'liveBarredModulesRead':False,'authorOrChildContact':False,'rootCoordinationOnly':True,'freshContextRefereePassCompleted':False}
(H/'POST-RELEASE-CONTACTS-v1.json').write_text(json.dumps(contacts,indent=2)+'\n')
shutil.copytree(H,DEST,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
shutil.copyfile(REVIEW/'SOL-FOREST-REDUCTIONS-WORKFILE-v1.md',DEST/'WORKFILE-POST-RELEASE-v1.md');shutil.copyfile(REVIEW/'TARGET-v1.md',DEST/'ROOT-TARGET-v1.md')
files=[{'path':str(p.relative_to(DEST)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(DEST.rglob('*')) if p.is_file()]
verdict=json.loads((H/'SCOPED-VERDICT-v1.json').read_text());manifest={'status':verdict['grade'],'sealUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'priorReadyManifestSHA256':readyhash,'priorReadyArtifactsRechecked':264,'releasedAuthorEntriesRechecked':180,'sourceModuleCount':25,'candidateSourcesEdited':False,'allThreeMainMilestones':'OPEN','verifiedClosed':False,'verdict':verdict,'artifactCount':len(files),'files':files}
mp=DEST/'REVIEW-MANIFEST-v1.json';mp.write_text(json.dumps(manifest,indent=2)+'\n');digest=sha(mp);(DEST/'REVIEW-MANIFEST-v1.sha256').write_text(digest+'  REVIEW-MANIFEST-v1.json\n')
assert all(sha(DEST/r['path'])==r['sha256'] for r in files)
for p in sorted(DEST.rglob('*'),reverse=True):os.chmod(p,0o555 if p.is_dir() else 0o444)
os.chmod(DEST,0o555)
print(json.dumps({'status':manifest['status'],'artifactCount':len(files),'manifest':str(mp),'manifestSHA256':digest,'readOnly':True,'allThreeMainMilestones':'OPEN'}))
