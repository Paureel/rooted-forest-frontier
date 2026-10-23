#!/usr/bin/env python3
"""One-shot preparation freeze; no scientific candidate access."""
import datetime,hashlib,json,os,pathlib,platform,shutil,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent; ROOT=HERE.parents[5]; REVIEW=HERE.parent
FROZEN=REVIEW/'sol-frozen-ready-v1'
if FROZEN.exists(): raise SystemExit('refuse overwrite of immutable freeze')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
contacts=[
 ('research/rmaf/algorithm/verification/forest-reductions-2026-10-15/TARGET-v1.md','root pin, first read'),
 ('bootloops/tools/README.md','toolkit capability index'),
 *[(f'.agents/skills/{s}/SKILL.md','applicable skill, fully read with truncated-output rereads noted in workfile') for s in ['prove-protocol','reading-contract','independence-bookkeeping','planted-truth','timing-discipline','tool-stewardship','acceptance-gate']],
 ('bootloops/tools/gatekeeper/GUIDE.md','nearest integrity guide, no checker implementation contacted'),
 ('bootloops/tools/emitall/GUIDE.md','nearest claims-integrity guide, no checker implementation contacted'),
 ('research/rmaf/algorithm/universal233/state_reductions/State.lean','allowed public interface, full definitions only; no theorem bodies present'),
 ('research/rmaf/lean/RMAF.lean','original definition ranges1–18,36–45,76–94,105–159; boundary fragments of original proofs disclosed'),
 ('research/rmaf/lean/lean-toolchain','runtime identification'),
 ('.runtime/elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Lean/Environment.lean','validation API ranges/searches enumerated in workfile; not scientific candidate'),
 ('.runtime/elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Lean/Util/CollectAxioms.lean','validation API90–165'),
 ('.runtime/elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Lean/Meta/Eqns.lean','validation API235–272 and symbol lookup'),
 ('bootloops-check','validation wrapper source and help/targeted package execution')]
contactData={'records':[{'path':p,'sha256AtFreeze':sha(ROOT/p),'contact':d} for p,d in contacts], 'otherContacts':['filename-only scoped discovery returned review/build filenames; none opened','one absent StatePartition filename query, no body read','parent coordination messages only; no author/reviewer scientific communication or children'], 'barredContacts':{'candidateProofs':False,'authorControls':False,'authorReceipts':False,'authorAuditors':False,'otherReviewerImplementations':False,'unfinishedMainOrChildren':False}}
(HERE/'CONTACTS-v1.json').write_text(json.dumps(contactData,indent=2)+'\n')
lean=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
version=subprocess.run([str(lean),'--version'],text=True,stdout=subprocess.PIPE,check=True).stdout.strip()
(HERE/'RUNTIME-v1.json').write_text(json.dumps({'lean':version,'python':sys.version,'pythonExecutable':sys.executable,'platform':platform.platform(),'allComputeLocal':True,'toolkitValidation':{'packages':['emitall','gatekeeper'],'passed':2,'fullSuiteRun':False},'scientificCandidateCompiled':False},indent=2)+'\n')
FROZEN.mkdir()
shutil.copytree(HERE,FROZEN/'preparation',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
shutil.copyfile(REVIEW/'SOL-FOREST-REDUCTIONS-WORKFILE-v1.md',FROZEN/'WORKFILE-v1.md')
shutil.copyfile(REVIEW/'TARGET-v1.md',FROZEN/'TARGET-v1.md')
files=[{'path':str(p.relative_to(FROZEN)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(FROZEN.rglob('*')) if p.is_file()]
manifest={'status':'PRE-CANDIDATE-READY','freezeUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifactCount':len(files),'files':files,'candidateReleased':False,'candidateCompiled':False,'mainMilestones':'all three OPEN','scientificGrade':'no candidate verdict; no VERIFIED-CLOSED grade','summary':{'states':21,'validAgreements':59,'singletonForward':5,'singletonReverse':5,'coalescingForward':40,'cherryReverse':17,'treeRoundtrips':8,'semanticMutationCatches':10,'fixedAuditCorruptionCatches':9,'standardAxiomPositiveTwins':3,'standardAxiomNegativeTwins':3,'toolkitSelftestsPassed':2},'releaseNeeded':'separate root release of exact completed singleton77+cherry103 source manifests'}
mp=FROZEN/'READY-MANIFEST-v1.json'; mp.write_text(json.dumps(manifest,indent=2)+'\n'); digest=sha(mp)
(FROZEN/'READY-MANIFEST-v1.sha256').write_text(digest+'  READY-MANIFEST-v1.json\n')
# Verify all retained bytes immediately before making the snapshot read-only.
assert all(sha(FROZEN/r['path'])==r['sha256'] for r in files)
for p in sorted(FROZEN.rglob('*'),reverse=True): os.chmod(p,0o555 if p.is_dir() else 0o444)
os.chmod(FROZEN,0o555)
print(json.dumps({'status':manifest['status'],'directory':str(FROZEN),'artifactCount':len(files),'manifestSHA256':digest,'readOnly':True}))
