#!/usr/bin/env python3
"""Bounded NEW-module-only audit; dependency hardlinks are read-only pins."""
from pathlib import Path
import datetime,gzip,hashlib,json,shutil,sys
sys.dont_write_bytecode=True
import instrument,pilot
D=pilot.D;R=pilot.R;O=pilot.O
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
spec=json.loads((D/'ROOT-v1.json').read_text())
mods=['SizePrecontrols','FrontierSupport','BoundedFrontier','SizeControls']
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def deps():
 for m in spec['manifests']:pin(R/m['path'],m['sha256'])
 for e in spec['dependencies']:
  for f in e['files']:
   for k in ['original','linked']:
    p=R/f[k];pin(p,f['sha256']);st=p.stat();assert not st.st_mode&0o222,'MUTABLE_DEPENDENCY';assert (st.st_ino,st.st_dev)==(f['inode'],f['device']),'INODE_CHANGED'
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');C=O/('certificate-'+stamp+'.json');F=O/('producer-records-'+stamp);F.mkdir();(O/('audit-'+stamp+'.source.py')).write_bytes((D/'audit.py').read_bytes())
rec={'status':'RUNNING_AUTHOR_FOREST_SIZE_AUDIT','independent_credit':0,'main_milestones':'ALL_OPEN','root':str(O.relative_to(R)),
 'new_modules':[],'dependency_modules':len(spec['dependencies']),'root_pin_sha256':sha(D/'ROOT-v1.json'),'producer_preflight':spec['producer_preflight'],
 'instrument_sha256':sha(D/'instrument.py'),'runs':[],'input_hashes':{},'module_timeout_seconds':30,'live_disk_floor_bytes':3*1024**3,
 'producer_uncompressed_cap_bytes':8388608,'compressed_total_cap_bytes':256*1024**2,
 'audit_scope':'Four new stored producers only; full nonproof/opaque bodies retained. Theorem proof TEXT omitted only with actual ConstantInfo.getUsedConstantsAsSet references/full AX closure. All 97 readonly imported source/olean hardlink pairs pinned to the completed frozen frontier author release; no dependency rebuilt or mutated.'}
def save():C.write_text(json.dumps(rec,indent=2)+'\n')
def run(n,want=0):
 before=set(O.glob(n+'-*.run.json'));s=pilot.run(n,want=want);p=next(iter(set(O.glob(n+'-*.run.json'))-before));rec['runs'].append({'path':str(p.relative_to(R)),'sha256':sha(p)});save();return s
save()
try:
 pin(D/'instrument.py',spec['instrument_sha256']);pre=spec['producer_preflight'];P=R/pre['manifest'];pin(P,pre['sha256']);pc=json.loads(P.read_text());pin(D/'instrument.py',pc['instrument_sha256'])
 for e in pc['immutable_files']:pin(R/e['path'],e['sha256'])
 for n in ['RMAF','ForestWork']:
  try:pilot.run(n)
  except RuntimeError as e:assert str(e)=='REFUSE_LINKED_DEPENDENCY_COMPILATION|'+n
  else:raise AssertionError('DEPENDENCY_COMPILE_GUARD_FAILED')
 assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
 assert hashlib.sha256(b'abc').hexdigest()!=hashlib.sha256(b'abd').hexdigest()
 deps()
 for n in mods:
  p=D/(n+'.lean');pin(O/p.name,sha(p));assert (O/(n+'.olean')).exists()
  ok=[q for q in O.glob(n+'-*.run.json') if (lambda x:x['exit']==0 and not x['failure'] and x['source_sha256']==sha(p))(json.loads(q.read_text()))];assert ok,'MISSING_EXACT_BUILD|'+n;q=max(ok,key=lambda p:p.stat().st_mtime_ns)
  rec['new_modules'].append({'module':n,'source':str(p.relative_to(R)),'source_sha256':sha(p),'compiled_source':str((O/p.name).relative_to(R)),'olean':str((O/(n+'.olean')).relative_to(R)),'olean_sha256':sha(O/(n+'.olean')),'build_receipt':str(q.relative_to(R)),'build_receipt_sha256':sha(q)})
 for n in ['TARGET-v1.md','CONTROLS-v1.md','ROOT-v1.json','instrument.py','pilot.py','prepare.py','audit.py','SizeFalsePrecontrols.lean','SizeFalseControls.lean','README.md','FIRST-GAP-v1.md','PROVENANCE-v1.md','PROSE-REVIEW-v1.md']:
  rec['input_hashes'][str((D/n).relative_to(R))]=sha(D/n)
 for n,count in [('SizeFalsePrecontrols',4),('SizeFalseControls',4)]:
  ok=[q for q in O.glob(n+'-*.run.json') if (lambda x:x['exit']==1 and not x['failure'] and x['source_sha256']==sha(D/(n+'.lean')))(json.loads(q.read_text()))];assert ok;q=max(ok,key=lambda p:p.stat().st_mtime_ns);x=json.loads(q.read_text());log=q.with_name(q.name.replace('.run.json','.log.gz'));s=gzip.open(log,'rt').read();assert s.count('is false')==count,'FALSE_SOURCE_CONTROL_FAILED'
  rec.setdefault('false_controls',[]).append({'source':str((D/(n+'.lean')).relative_to(R)),'receipt':str(q.relative_to(R)),'sha256':sha(q),'actual_false_rejections':count})
 save()
 for n,text,want in [('SizeStdTrue','import Std\nexample : (3:Nat)+4=7 := by decide\n',0),('SizeStdFalse','import Std\nexample : (3:Nat)+4=8 := by decide\n',1)]:
  (O/(n+'.lean')).write_text(text);s=run(n,want)
  if want:assert s.count('is false')==1
 (O/'SizeAudit.lean').write_text(instrument.source(['SizeControls'],mods,F));run('SizeAudit');rows=instrument.parse(F,mods,O)
 assert sum(p.stat().st_size for p in F.glob('*.gz'))<256*1024**2
 names=['schedule_query_support','frontier_query_support','frontier_query_size','frontier_work_bound_on_queries','frontier_work_bound_size_capped','source_work_bound_on_queries','source_work_bound_size_capped']
 required=['GenericForest.FrontierSize.'+n for n in names]
 for n in required:assert any(r['name']==n and r['kind']=='theorem' for r in rows),n
 byname={r['name']:r for r in rows};runtime_names=['SizeCappedOrdinaryBillBound'];runtime={n:byname['GenericForest.FrontierSize.'+n] for n in runtime_names}
 for n,r in runtime.items():
  assert r['kind']=='definition' and r['body'] is not None
  assert not any(any(bad in x for bad in ['ghost','minimumCallback','OrdinaryIH','BelowIH','ExactSolverHyp','Classical.choose']) for x in r['references']),n
 for n in ['frontier_work_bound_on_queries','frontier_work_bound_size_capped','source_work_bound_on_queries','source_work_bound_size_capped']:
  r=byname['GenericForest.FrontierSize.'+n];assert 'OrdinaryIH' not in r['type'] and 'BelowIH' not in r['type'] and 'ExactSolverHyp' not in r['type'] and 'GenericForest.FrontierWork.OrdinaryBillBound' not in r['type']
 r=byname['GenericForest.FrontierSize.source_work_bound_size_capped'];assert 'LocalOverheadBound' in r['type'] and 'SizeCappedOrdinaryBillBound' in r['type']
 r=byname['GenericForest.FrontierSize.frontier_work_bound_on_queries'];assert 'GenericForest.FrontierWork.frontier' in r['type']

 deps()
 for e in rec['new_modules']:pin(R/e['source'],e['source_sha256']);pin(R/e['compiled_source'],e['source_sha256']);pin(R/e['olean'],e['olean_sha256'])
 for p,h in rec['input_hashes'].items():pin(R/p,h)
 rec.update(status='PASS_AUTHOR_FOREST_SIZE_BINDING_OPEN',new_source_modules=len(mods),stored_new_producer_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=required,runtime_direct_references={n:r['references'] for n,r in runtime.items()},runtime_ghost_used=False,global_ordinary_ih_premise=False,producer_files=[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in sorted(F.iterdir())],fresh_source_control_rejections=8,first_unprovided_main_call='Bound selected generationBill using frozen meterGenerate prefix envelope and literal color/address cost; then derive polynomial zero-work local K including every raw materialization and inspection.',skipped=['whole imported-pool rebuild','fresh imported-declaration audit','new extractor changes','imported all-stored runtime IR claim','primitive-source-bill correspondence','concrete polynomial local overhead K','independent semantic/interface/prose acceptance','full algorithm/base/runtime/novelty acceptance'])
 save();(D/'LATEST-REPLAY-v1.json').write_text(json.dumps({'receipt':str(O.relative_to(R)),'certificate':str(C.relative_to(R)),'sha256':sha(C)},indent=2)+'\n');print(rec['status'],len(rows),'new stored occurrences; AX=',rec['axiom_union'],flush=True)
except BaseException as e:rec.update(status='FAILED_AUTHOR_FOREST_SIZE_AUDIT',error=repr(e));save();raise
