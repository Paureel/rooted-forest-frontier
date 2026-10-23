#!/usr/bin/env python3
"""Bounded new-producer checker audit. Exact controlled extractor unchanged."""
from pathlib import Path
import datetime,gzip,hashlib,json,sys
sys.dont_write_bytecode=True
import instrument,pilot
D=pilot.D;R=pilot.R;O=pilot.O;spec=json.loads((D/'ROOT-v1.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=['CheckPrecontrols','ReturnedPayload','CheckPrimitives','PartitionCost','TreeCheckMeters','HullCheckMeters','CheckFamilies','CheckAssembly','CheckBounds','InspectionBound','ActualCandidates','ActualInspection','CheckControls']
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def deps():
 for m in spec['manifests']:pin(R/m['path'],m['sha256'])
 for e in spec['dependencies']:
  for f in e['files']:
   p=R/f['original'];pin(p,f['sha256']);assert oct(p.stat().st_mode&0o777)==f['original_mode'],'ORIGINAL_MODE_CHANGED'
   p=R/f['linked'];pin(p,f['sha256']);st=p.stat();assert not st.st_mode&0o222,'MUTABLE_SNAPSHOT';assert (st.st_ino,st.st_dev)==(f['inode'],f['device']),'SNAPSHOT_INODE_CHANGED'
 for e in spec['identical_source_contacts']:
  f=e['identical'];p=R/f['original'];pin(p,f['sha256']);assert oct(p.stat().st_mode&0o777)==f['original_mode']
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');C=O/('certificate-'+stamp+'.json');F=O/('producer-records-'+stamp);F.mkdir();(O/('audit-'+stamp+'.source.py')).write_bytes((D/'audit.py').read_bytes())
rec={'status':'RUNNING_AUTHOR_FOREST_CHECK_AUDIT','independent_credit':0,'main_milestones':'ALL_OPEN','root':str(O.relative_to(R)),'new_modules':[],'dependency_modules':len(spec['dependencies']),'root_pin_sha256':sha(D/'ROOT-v1.json'),'producer_preflight':spec['producer_preflight'],'instrument_sha256':sha(D/'instrument.py'),'runs':[],'input_hashes':{},'module_timeout_seconds':30,'live_disk_floor_bytes':3*1024**3,'producer_uncompressed_cap_bytes':8388608,'compressed_total_cap_bytes':256*1024**2,'audit_scope':'13 new stored producers only; all nonproof/opaque bodies retained; theorem proof TEXT omitted only with actual full proof references and AX walk. 443 exact readonly imported source/olean snapshots pinned, originals modes unchanged; no imported all-stored IR or native scalar runtime claim.'}
def save():C.write_text(json.dumps(rec,indent=2)+'\n')
def run(n,want=0):
 before=set(O.glob(n+'-*.run.json'));s=pilot.run(n,want=want);p=next(iter(set(O.glob(n+'-*.run.json'))-before));rec['runs'].append({'path':str(p.relative_to(R)),'sha256':sha(p)});save();return s
save()
try:
 pin(D/'instrument.py',spec['instrument_sha256']);pre=spec['producer_preflight'];P=R/pre['manifest'];pin(P,pre['sha256']);pc=json.loads(P.read_text());pin(D/'instrument.py',pc['instrument_sha256'])
 for e in pc['immutable_files']:pin(R/e['path'],e['sha256'])
 for n in ['RMAF','ForestWork','FastExact']:
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
 for n in ['TARGET-v1.md','CONTROLS-v1.md','ROOT-v1.json','instrument.py','pilot.py','prepare.py','audit.py','CheckFalsePrecontrols.lean','CheckFalseControls.lean','README.md','FIRST-GAP-v1.md','PROVENANCE-v1.md','PROSE-REVIEW-v1.md']:
  rec['input_hashes'][str((D/n).relative_to(R))]=sha(D/n)
 for n,count in [('CheckFalsePrecontrols',4),('CheckFalseControls',6)]:
  ok=[q for q in O.glob(n+'-*.run.json') if (lambda x:x['exit']==1 and not x['failure'] and x['source_sha256']==sha(D/(n+'.lean')))(json.loads(q.read_text()))];assert ok;q=max(ok,key=lambda p:p.stat().st_mtime_ns);s=gzip.open(q.with_name(q.name.replace('.run.json','.log.gz')),'rt').read();assert s.count('is false')==count,'FALSE_SOURCE_CONTROL_FAILED'
  rec.setdefault('false_controls',[]).append({'source':str((D/(n+'.lean')).relative_to(R)),'receipt':str(q.relative_to(R)),'sha256':sha(q),'actual_false_rejections':count})
 save()
 for n,txt,want in [('CheckStdTrue','import Std\nexample : (3:Nat)+4=7 := by decide\n',0),('CheckStdFalse','import Std\nexample : (3:Nat)+4=8 := by decide\n',1)]:
  (O/(n+'.lean')).write_text(txt);s=run(n,want)
  if want:assert s.count('is false')==1
 (O/'CheckAudit.lean').write_text(instrument.source(['CheckControls'],mods,F));run('CheckAudit');rows=instrument.parse(F,mods,O)
 assert sum(p.stat().st_size for p in F.glob('*.gz'))<256*1024**2
 names=['fast_returned_payload','returned_payload_bit_cells','meterPartition_value','meterPartition_count_lower','hostile_partition_exceeds_inspection','meterRestrictionAgrees_value','meterPairwise_value','meterAgrees_value','meterAccepted_value','meterChecked_value','meterAgrees_cap','meterChecked_cap','checked_work_le_inspection','accepted_work_le_inspection','agrees_work_le_inspection','raw_checks_bound','actual_raw_checks_bound','jobs_payload','run_payload','scheduled_payload','proper_work_le_inspection','initial_check_bound','actual_singleton_check_bound','disjoint_attempt_check_bound','fast_actual_singleton_check_bound','fast_disjoint_attempt_check_bound']
 required=['GenericForest.CheckCorrespondence.'+n for n in names];byname={r['name']:r for r in rows}
 for n in required:assert n in byname and byname[n]['kind']=='theorem',n
 runtime_names=['meterAll','meterAny','meterCount','meterFlatten','meterPartition','meterSameShape','meterRestrict','meterRestrictionAgrees','meterDisjoint','meterHullPair','meterPairwise','meterLeaves','meterNodup','meterContained','meterFamily','meterSourceLeaves','meterLabels','meterProper','meterTargetAgrees','meterTargetEmbeddings','meterSourceCheck','meterSourceContainment','meterAgrees','meterAccepted','meterChecked','recursiveCandidates']
 runtime={n:byname['GenericForest.CheckCorrespondence.'+n] for n in runtime_names}
 for n,r in runtime.items():
  assert r['kind']=='definition' and r['body'] is not None
  assert not any(any(bad in x for bad in ['minimumCallback','OrdinaryIH','BelowIH','ExactSolverHyp','Classical.choose']) for x in r['references']),n
 for n in ['checked_work_le_inspection','proper_work_le_inspection','actual_raw_checks_bound']:
  r=byname['GenericForest.CheckCorrespondence.'+n];assert 'OrdinaryIH' not in r['type'] and 'BelowIH' not in r['type']
 for n in ['fast_actual_singleton_check_bound','fast_disjoint_attempt_check_bound']:
  assert 'FastOrdinary.solve' in byname['GenericForest.CheckCorrespondence.'+n]['type']
 deps()
 for e in rec['new_modules']:pin(R/e['source'],e['source_sha256']);pin(R/e['compiled_source'],e['source_sha256']);pin(R/e['olean'],e['olean_sha256'])
 for p,h in rec['input_hashes'].items():pin(R/p,h)
 rec.update(status='PASS_AUTHOR_FOREST_CHECK_UNIT_SCALAR_OPEN',new_source_modules=len(mods),stored_new_producer_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=required,runtime_direct_references={n:r['references'] for n,r in runtime.items()},runtime_ghost_used=False,producer_files=[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in sorted(F.iterdir())],fresh_source_control_rejections=10,first_unprovided_main_call='WholeSourceWork.meterContains scalar slot x==y costs unit4; prove explicit binary equality/order/arithmetic scalar algorithms and weighted checker lift in new forest_scalar_bit_lift scope. Native primitive body/bit runtime is not certified here.',skipped=['whole imported-pool rebuild','fresh imported-declaration audit','new extractor changes','imported all-stored runtime IR claim','native scalar primitive correspondence','independent semantic/interface/prose acceptance','full algorithm/base/runtime/novelty acceptance'])
 save();(D/'LATEST-REPLAY-v1.json').write_text(json.dumps({'receipt':str(O.relative_to(R)),'certificate':str(C.relative_to(R)),'sha256':sha(C)},indent=2)+'\n');print(rec['status'],len(rows),'new stored occurrences; AX=',rec['axiom_union'],flush=True)
except BaseException as e:rec.update(status='FAILED_AUTHOR_FOREST_CHECK_AUDIT',error=repr(e));save();raise
