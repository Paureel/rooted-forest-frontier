#!/usr/bin/env python3
"""Bounded audit of new overlap modules using the unchanged frozen extractor."""
from pathlib import Path
import datetime,hashlib,json,shutil,sys
sys.dont_write_bytecode=True
import instrument,pilot
D=Path(__file__).resolve().parent;R=pilot.R;O=pilot.O
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
spec=json.loads((D/'ROOT-v1.json').read_text());priority=json.loads((D/'PRIORITY-INPUT-v1.json').read_text())
dependencies=spec['dependencies']+priority['dependencies']
mods=['OverlapPrecontrols','OverlapDefs','SourceGuards','Exhaustive','ActualHard2','PaidConsumers','PairGuards','OverlapControls','LiteralProbe']
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def deps():
 for e in dependencies:
  for f in e['files']:
   for key in ['original','linked']:
    p=R/f[key];pin(p,f['sha256']);s=p.stat();assert s.st_ino==f['inode'] and s.st_dev==f['device'] and s.st_nlink>1 and not s.st_mode&0o222
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
C=O/('certificate-'+stamp+'.json');F=O/('producer-records-'+stamp);F.mkdir();(O/('audit-'+stamp+'.source.py')).write_bytes((D/'audit.py').read_bytes())
rec={'status':'RUNNING_AUTHOR_OVERLAP_AUDIT','independent_credit':0,'main_milestones':'ALL_OPEN','root':str(O.relative_to(R)),
 'new_modules':[],'dependency_modules':len(dependencies),'root_pin_sha256':sha(D/'ROOT-v1.json'),'priority_pin_sha256':sha(D/'PRIORITY-INPUT-v1.json'),
 'producer_preflight':spec['producer_preflight'],'instrument_sha256':sha(D/'instrument.py'),'runs':[],'input_hashes':{},
 'module_timeout_seconds':30,'live_disk_floor_bytes':3*1024**3,'producer_uncompressed_cap_bytes':8388608,'compressed_total_cap_bytes':256*1024**2,
 'audit_scope':'Nine new stored producer modules only. Full nonproof/opaque bodies retained. Theorem proof TEXT omitted only with actual ConstantInfo.getUsedConstantsAsSet references and full AX closure. All 318 imported source/olean dependencies pinned; none rebuilt.'}
def save():C.write_text(json.dumps(rec,indent=2)+'\n')
def run(n,want=0):
 before=set(O.glob(n+'-*.run.json'));s=pilot.run(n,want=want);q=next(iter(set(O.glob(n+'-*.run.json'))-before));rec['runs'].append({'path':str(q.relative_to(R)),'sha256':sha(q)});save();return s
save()
try:
 pin(D/'instrument.py',spec['instrument_sha256']);pre=spec['producer_preflight'];P=R/pre['manifest'];pin(P,pre['sha256']);pc=json.loads(P.read_text());pin(D/'instrument.py',pc['instrument_sha256'])
 for e in pc['immutable_files']:pin(R/e['path'],e['sha256'])
 for f in [spec['frozen_manifest'],priority['manifest']]:pin(R/f['path'],f['sha256'])
 # Fresh engine/source guards precede extraction; exact producer controls reused.
 try:pilot.run('RMAF')
 except RuntimeError as e:assert str(e)=='REFUSE_LINKED_DEPENDENCY_COMPILATION|RMAF'
 else:raise AssertionError('DEPENDENCY_COMPILE_GUARD_FAILED')
 assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
 assert hashlib.sha256(b'abc').hexdigest()!=hashlib.sha256(b'abd').hexdigest()
 deps()
 if shutil.disk_usage(D).free<3*1024**3:raise RuntimeError('DISK_FLOOR_3_GIB')
 for n in mods:
  p=D/(n+'.lean');pin(O/p.name,sha(p));assert (O/(n+'.olean')).exists()
  ok=[q for q in O.glob(n+'-*.run.json') if (lambda x:x['exit']==0 and not x['failure'] and x['source_sha256']==sha(p))(json.loads(q.read_text()))];assert ok,'MISSING_EXACT_BUILD|'+n;q=max(ok,key=lambda p:p.stat().st_mtime_ns)
  rec['new_modules'].append({'module':n,'source':str(p.relative_to(R)),'source_sha256':sha(p),'compiled_source':str((O/p.name).relative_to(R)),'olean':str((O/(n+'.olean')).relative_to(R)),'olean_sha256':sha(O/(n+'.olean')),'build_receipt':str(q.relative_to(R)),'build_receipt_sha256':sha(q)})
 for n in ['TARGET-v1.md','CONTROLS-PIN-v1.md','ROOT-v1.json','PRIORITY-INPUT-v1.json','instrument.py','pilot.py','audit.py','OverlapFalsePrecontrols.lean','OverlapFalseControls.lean']:
  rec['input_hashes'][str((D/n).relative_to(R))]=sha(D/n)
 for n,count in [('OverlapFalsePrecontrols',4),('OverlapFalseControls',7)]:
  ok=[q for q in O.glob(n+'-*.run.json') if (lambda x:x['exit']==1 and not x['failure'] and x['source_sha256']==sha(D/(n+'.lean')))(json.loads(q.read_text()))];assert ok;q=max(ok,key=lambda p:p.stat().st_mtime_ns)
  rec.setdefault('false_controls',[]).append({'source':str((D/(n+'.lean')).relative_to(R)),'receipt':str(q.relative_to(R)),'sha256':sha(q),'actual_false_rejections':count})
 save()
 for n,text,want in [('OverlapStdTrue','import Std\nexample : (3:Nat)+4=7 := by decide\n',0),('OverlapStdFalse','import Std\nexample : (3:Nat)+4=8 := by decide\n',1)]:
  (O/(n+'.lean')).write_text(text);s=run(n,want)
  if want:assert s.count('is false')==1
 (O/'OverlapAudit.lean').write_text(instrument.source(['OverlapControls','LiteralProbe'],mods,F));run('OverlapAudit');rows=instrument.parse(F,mods,O)
 assert sum(p.stat().st_size for p in F.glob('*.gz'))<256*1024**2
 names=['parents_perm','overlap_sound','overlap_none','partition_pair_proper','chain_guards','chain_valid','isolated_valid','select_exhaustive','select_sound','actual_source_inputs','actual_hard2_exhaustive','actual_disjoint_admission_iff','actual_clique_paid','actual_four_paid','actual_diagonal_paid','selected_pair_guards','actual_vertex_pair_paid']
 required=['Universal233.Hard2Overlap.'+n for n in names]
 for n in required:assert any(r['name']==n and r['kind']=='theorem' for r in rows),n
 runtime={}
 for n in ['overlap','chain','isolated','select','runHard2']:
  rr=next(r for r in rows if r['name']=='Universal233.Hard2Overlap.'+n);assert rr['kind']=='definition' and rr['body'] is not None
  assert not any(any(bad in x for bad in ['Ghost','Covered','rawQMass','OrdinaryIH','RefinesBlocks','agreement']) for x in rr['references'])
  runtime[n]=rr['references']
 for n in ['actual_first_overlap_selected','actual_pair_both_bad']:
  assert any(r['name']=='Universal233.Hard2Overlap.Controls.'+n and r['kind']=='theorem' for r in rows)
 deps()
 for e in rec['new_modules']:pin(R/e['source'],e['source_sha256']);pin(R/e['compiled_source'],e['source_sha256']);pin(R/e['olean'],e['olean_sha256'])
 for p,h in rec['input_hashes'].items():pin(R/p,h)
 rec.update(status='PASS_AUTHOR_ACTUAL_HARD2_OVERLAP_SELECTOR_OPEN',new_source_modules=len(mods),stored_new_producer_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=required,runtime_direct_references=runtime,producer_files=[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in sorted(F.iterdir())],fresh_source_control_rejections=11,first_unprovided_main_call='Total dispatcher execution and current-budget callback binding for every selected geometry; disjoint good-block-count classification and isolated edge good/bad-parent program selection remain literal decisions. Actual first common fixture is an isolated vertex pair and its paid cover/mass are consumed.',skipped=['whole imported-pool rebuild','raw dependency record dumps','new extractor changes','independent semantic/interface/prose acceptance','full algorithm/base/runtime/novelty acceptance'])
 save();(D/'LATEST-REPLAY-v1.json').write_text(json.dumps({'receipt':str(O.relative_to(R)),'certificate':str(C.relative_to(R)),'sha256':sha(C)},indent=2)+'\n');print(rec['status'],len(rows),'new stored occurrences; AX=',rec['axiom_union'],flush=True)
except BaseException as e:rec.update(status='FAILED_AUTHOR_OVERLAP_AUDIT',error=repr(e));save();raise
