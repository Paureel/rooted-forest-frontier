#!/usr/bin/env python3
"""One-shot thin source/olean extension. No raw producer records copied.
The unchanged bounded compiler/extractor and exact frozen control receipt
are reused; only three new modules are source-built and audited here.
"""
from pathlib import Path
import datetime,gzip,hashlib,json,shutil,sys
sys.dont_write_bytecode=True
import instrument,pilot
D=Path(__file__).resolve().parent;R=D.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
I=D/'INPUTS-v1.json';inputs=json.loads(I.read_text());assert inputs['status']=='PASS_THIN_FROZEN_EXTENSION_PREPARE'
for k in ['selector_manifest','local_ih_manifest']:pin(R/inputs[k]['path'],inputs[k]['sha256'])
pin(D/'instrument.py',inputs['instrument_sha256']);pin(D/'pilot.py',inputs['pilot_sha256'])
P=inputs['producer_preflight'];M=R/P['manifest'];pin(M,P['sha256']);pc=json.loads(M.read_text());pin(D/'instrument.py',pc['instrument_sha256'])
for e in pc['immutable_files']:pin(R/e['path'],e['sha256'])
if shutil.disk_usage(D).free<3*1024**3:raise RuntimeError('DISK_FLOOR_3_GIB')
O=R/'results'/('algorithm-universal233-rule5-common-ordinary-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir();(O/'lean-toolchain').write_bytes((D/'build/lean-toolchain').read_bytes())
record={'status':'RUNNING_AUTHOR_THIN_EXTENSION','independent_credit':0,'main_milestones':'ALL_OPEN','inputs_sha256':sha(I),'producer_preflight':P,'dependency_modules':inputs['frozen_dependencies'],'new_modules':[],'runs':[],'input_hashes':{},'module_timeout_seconds':30,'disk_floor_bytes':3*1024**3,'audit_scope':'Theorem proof TEXT omitted only; actual ConstantInfo proof references and AX closures retained; full nonproof/opaque bodies kept.'}
def save():(O/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
for e in record['dependency_modules']:
 for field,hkey,suffix in [('source','source_sha256','.lean'),('olean','olean_sha256','.olean')]:
  p=R/e[field];pin(p,e[hkey]);shutil.copyfile(p,O/(e['module']+suffix))
new=[('ForestMinimumCompletion',R/inputs['new_source_inputs'][0]['source'])]+[(n,D/(n+'.lean')) for n in ['OrdinaryBinding','BindingControls']]
for n,p in new:
 (O/(n+'.lean')).write_bytes(p.read_bytes());record['new_modules'].append({'module':n,'source':str(p.relative_to(R)),'sha256':sha(p)})
(O/'BindingFalseControls.lean').write_bytes((D/'BindingFalseControls.lean').read_bytes())
for n in ['README.md','TARGET-v1.md','FIRST-GAP-v1.md','CONTROLS-PIN-v1.md','PROVENANCE-v1.md','replay.py','INPUTS-v1.json','instrument.py','pilot.py']:
 p=D/n;record['input_hashes'][str(p.relative_to(R))]=sha(p);(O/n).write_bytes(p.read_bytes())
save()
def run(n,build=False,want=0):
 before=set(O.glob(n+'-*.log.gz'));out=pilot.run(O,n,build,want);log=next(iter(set(O.glob(n+'-*.log.gz'))-before));record['runs'].append({'module':n,'expected_exit':want,'log':str(log.relative_to(R)),'sha256':sha(log)});save();return out
try:
 for n,text,w in [('StdTrue','import Std\nexample : (3:Nat)+4=7 := by decide\n',0),('StdFalse','import Std\nexample : (3:Nat)+4=8 := by decide\n',1)]:
  (O/(n+'.lean')).write_text(text);s=run(n,want=w)
  if w:assert s.count('is false')==1
 for n,p in new:run(n,True)
 s=run('BindingFalseControls',want=1);assert s.count('is false')==5
 F=O/'producer-records';F.mkdir();mods=[n for n,p in new];(O/'ExtensionAudit.lean').write_text(instrument.source(['BindingControls'],mods,F));run('ExtensionAudit');rows=instrument.parse(F,mods,O)
 assert sum(p.stat().st_size for p in F.glob('*.gz'))<256*1024**2
 required=['Universal233.Rule5CommonOrdinary.'+n for n in ['runSelectedCommon','local_callback_bounded','callback_jobs_below','actual_source_ih','selected_bounded','selected_sound_minimum','selected_complete','selected_none_iff']]
 for n in required:assert any(r['name']==n for r in rows),n
 runrow=next(r for r in rows if r['name']=='Universal233.Rule5CommonOrdinary.runSelectedCommon');assert runrow['kind']=='definition' and runrow['body'] is not None
 assert 'Universal233.Rule5CommonSelector.runCommon' in runrow['references']
 assert not any('ghost' in n or 'minimumCallback' in n or 'OrdinaryIH' in n for n in runrow['references'])
 ihrow=next(r for r in rows if r['name']=='Universal233.Rule5CommonOrdinary.actual_source_ih');assert 'ForestMinCompletion.LocalOrdinaryIH' in ihrow['type'];assert 'GenericForest.OrdinaryIH' not in ihrow['type']
 for e in record['dependency_modules']:pin(R/e['source'],e['source_sha256']);pin(R/e['olean'],e['olean_sha256']);pin(O/(e['module']+'.lean'),e['source_sha256']);pin(O/(e['module']+'.olean'),e['olean_sha256'])
 for e in record['new_modules']:pin(R/e['source'],e['sha256']);pin(O/(e['module']+'.lean'),e['sha256'])
 for p,h in record['input_hashes'].items():pin(R/p,h)
 record.update(status='PASS_AUTHOR_BUDGET_LOCAL_SELECTED_COMMON_OPEN',new_source_builds=len(new),pinned_dependency_modules=len(record['dependency_modules']),stored_new_producer_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=required,executable_direct_references=runrow['references'],runtime_ghost_used=False,global_ordinary_ih_premise=False,false_mathematical_rejections=5,producer_files=[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in sorted(F.iterdir())],first_unprovided_main_call='parent total ordinary dispatcher, current-budget recursive binding/termination and source/bit/payload recurrence',skipped=['whole dependency-pool rebuild','raw record copy','toolkit-wide suite','fresh nonauthor semantic/interface/prose review','main algorithm/base/novelty acceptance'])
 save();(O/'VERDICT.txt').write_text(record['status']+'\nThree-module author extension;315 prior source/olean dependencies pinned. Main milestones and independent acceptance OPEN.\n');(D/'LATEST-REPLAY-v1.json').write_text(json.dumps({'receipt':str(O.relative_to(R)),'sha256':sha(O/'certificate.json')},indent=2)+'\n');print(record['status'],len(new),'source builds;',len(rows),'new stored occurrences;',O,flush=True)
except BaseException as e:record['status']='FAILED_AUTHOR_THIN_EXTENSION';record['error']=repr(e);save();raise
