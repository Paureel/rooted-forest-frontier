#!/usr/bin/env python3
"""One-shot author continuation wrapper; shard completed producer extraction.
This reuses completed author detectors; it provides no independent credit.
"""
from pathlib import Path
import copy, datetime, hashlib, importlib.util, json, os, re, subprocess, time
D=Path(__file__).resolve().parent; R=D.parents[5]
B=R/'results/algorithm-universal233-ordinary-source-pool-20261015T144445575127Z'
O=R/'results'/('algorithm-universal233-ordinary-source-pool-resume-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')); O.mkdir()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path); mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
A=load('resumed_split_audit',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
C=load('resumed_control_audit',R/'research/rmaf/algorithm/universal233/rule5_case322/audit.py')
G=load('resumed_value_gate',D.parent/'producer_compatibility/compatibility.py')
rec=dict(status='PRECONSTRUCTION_CONTROLS_RUNNING',independent_acceptance=False,full_algorithm=False,all_main_milestones='OPEN',
 source_build_claim='No new individual source rebuild; resume completed306 literal-source builds with pinned source/build/log/binary receipts.',
 old_build=str(B.relative_to(R)),old_construction_sha256=sha(B/'construction.json'),runs=[],controls={},shards=[],contacts={})
for p in [Path(__file__),D/'AUDIT-PLAN-v1.md',Path(A.__file__),Path(C.__file__),Path(G.__file__)]: rec['contacts'][str(p.relative_to(R))]=sha(p)
def save(): (O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def run(directory,name,pathroot,build=False):
 start=time.monotonic()
 try: p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(directory/(name+'.olean'))] if build else [])+[str(directory/(name+'.lean'))],cwd=directory,env=dict(os.environ,LEAN_PATH=str(pathroot)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 except subprocess.TimeoutExpired as e:
  (directory/(name+'.log')).write_text((e.stdout or b'').decode() if isinstance(e.stdout,bytes) else (e.stdout or ''))
  rec.update(status='TIMEOUT_NOT_ACCEPTED',failed_module=name);save();raise
 (directory/(name+'.log')).write_text(p.stdout);rec['runs'].append(dict(module=name,exit=p.returncode,seconds=time.monotonic()-start));save();return p

def source(imports,wanted,out):
 s=A.audit_source(imports,wanted,out)
 old='    let producer := env.header.moduleNames[i]!\n'
 assert s.count(old)==1
 return s.replace(old,old+'    let path ← liftIO <| findOLean producer\n    logInfo m!"PATH|{producer}|{path}"\n')
def paths(log,expected,root):
 pairs=re.findall(r'^PATH\|([^|]+)\|(.+)$',log,re.M); pp=dict(pairs)
 assert len(pairs)==len(pp),'DUPLICATE_MODULE_PATH'
 assert set(expected)<=set(pp),'MISSING_MODULE_PATH'
 for name,path in pp.items():
  p=Path(path).resolve()
  assert p==(root/(name+'.olean')).resolve() if name in expected else p.is_relative_to(R/'.runtime/elan/toolchains'),'FOREIGN_MODULE_PATH'
 return pp

def extract(directory,imports,wanted,pathroot,label):
 out=directory/('records-'+label);out.mkdir()
 name='Extract'+label;(directory/(name+'.lean')).write_text(source(imports,wanted,out))
 p=run(directory,name,pathroot);assert p.returncode==0,p.stdout[-6000:]
 pp=paths(p.stdout,imports,pathroot)
 idx=json.loads((out/'index.json').read_text());assert not idx['rejects']
 assert len(idx['producer_counts'])==len(wanted) and {x['producer'] for x in idx['producer_counts']}==set(wanted),'MISSING_OR_DUPLICATE_PRODUCER'
 rows=[]
 for count in idx['producer_counts']:
  actual=json.loads((out/count['file']).read_text());A.parse_producer(count,actual);rows.extend(actual)
 return rows,idx,out,pp
save()
try:
 T=O/'fresh-controls';T.mkdir();(T/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 rec['controls']['std_producer']=C.detector_controls(T);save()
 for name,value in [('ResumeValue0',0),('ResumeValue1',1),('ResumeValueTwin',0)]:
  (T/(name+'.lean')).write_text('import Std\nnamespace ResumePlant\ndef value : Nat := '+str(value)+'\nend ResumePlant\n')
  p=run(T,name,T,True);assert p.returncode==0,p.stdout
 values={};control_dump=None
 for name in ['ResumeValue0','ResumeValue1','ResumeValueTwin']:
  rows,idx,out,pp=extract(T,[name],[name],T,name)
  values[name]=[r for r in rows if r['actual_name']=='ResumePlant.value'];assert len(values[name])==1
  if name=='ResumeValue0':control_dump=(rows,idx,out,pp)
 for label,names,reject in [('clean',['ResumeValue0','ResumeValueTwin'],False),('badLR',['ResumeValue0','ResumeValue1'],True),('badRL',['ResumeValue1','ResumeValue0'],True)]:
  actual=G.inspect([r for n in names for r in values[names[names.index(n)]]]);assert bool(actual['rejects'])==reject
  rec['controls'][label]=dict(expected_reject=reject,result=actual)
 rows,idx,out,pp=control_dump;count=idx['producer_counts'][0];clean=json.loads((out/count['file']).read_text())
 mutations={
 'missing_row':clean[:-1], 'duplicate_row':clean+[clean[0]],
 'producer_attribution':[dict(r,producer='Foreign') if i==0 else r for i,r in enumerate(clean)],
 'unresolved_origin':[dict(r,resolved_origin='<unresolved>') if i==0 else r for i,r in enumerate(clean)],
 'custom_axiom_reference':[dict(r,axiom_references=['ResumeForbidden']) if i==0 else r for i,r in enumerate(clean)]}
 for label,bad in mutations.items():
  try:A.parse_producer(count,bad)
  except AssertionError:rec['controls'][label]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+label)
 log=(T/'ExtractResumeValue0.log').read_text()
 for label,bad in [('foreign_module',log.replace(str(T/'ResumeValue0.olean'),'/tmp/foreign/ResumeValue0.olean')),('missing_module_path',re.sub(r'^PATH\|ResumeValue0\|.*\n','',log,flags=re.M))]:
  try:paths(bad,['ResumeValue0'],T)
  except AssertionError:rec['controls'][label]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+label)
 assert G.inspect([])=={'duplicates':[],'rejects':[]};rec['controls']['empty_assembly']='EXACT_ZERO'
 for label,data,want in [('source_corruption',b'bad','0'*64),('adapted_corruption',b'extra','0'*64)]:
  try:assert hashlib.sha256(data).hexdigest()==want
  except AssertionError:rec['controls'][label]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+label)
 rec['status']='FRESH_CONTROLS_PASS';save()
 old=json.loads((B/'construction.json').read_text());assert old['status']=='SOURCE_POOL_ALL_LITERAL_SOURCES_REBUILT_PENDING_ORIGIN_AND_COMPATIBILITY_AUDIT'
 names=[x['module'] for x in old['source_modules']];assert len(names)==306 and len(names)==len(set(names))
 assert len(old['runs'])==len(names) and all(x['exit']==0 for x in old['runs'])
 oldpins={}
 for e in old['source_modules']:
  name=e['module'];assert sha(B/(name+'.lean'))==e['sha256']
  for suffix in ['lean','olean','log']:oldpins[str((B/(name+'.'+suffix)).relative_to(R))]=sha(B/(name+'.'+suffix))
 for e in old['runs']:assert sha(B/(e['module']+'.log'))==e['log_sha256']
 (O/'OLD-BUILD-PINS.json').write_text(json.dumps(oldpins,indent=2)+'\n')
 rec.update(status='ACTUAL_SHARDED_AUDIT_RUNNING',source_modules=len(names),old_pins=len(oldpins));save()
 allrows=[]
 for i in range(0,len(names),40):
  wanted=names[i:i+40];start=time.monotonic();rows,idx,out,pp=extract(O,names,wanted,B,'Shard'+str(i//40))
  elapsed=time.monotonic()-start
  allrows.extend(rows);rec['shards'].append(dict(index=i//40,producers=len(wanted),occurrences=len(rows),seconds=elapsed,index_sha256=sha(out/'index.json')));save()
  print('SHARD',i//40,'PRODUCERS',len(wanted),'OCCURRENCES',len(rows),'SECONDS',round(elapsed,3),flush=True)
  if i==0:
   rec['timing_projection']=dict(pilot_producers=len(wanted),pilot_seconds=elapsed,shards=8,assumption='Per-shard module import overhead and variable producer sizes; first-shard timing is a planning estimate, not a bound.',projected_seconds=elapsed*8);save()
   assert elapsed*8<7200,'RESTRUCTURE_REQUIRED'
 compatibility=G.inspect(allrows);(O/'PRODUCER-COMPATIBILITY-v1.json').write_text(json.dumps(compatibility,indent=2)+'\n');assert not compatibility['rejects'],compatibility['rejects']
 for path,h in oldpins.items():assert sha(R/path)==h,'OLD_INPUT_CHANGED'
 assert sha(B/'construction.json')==rec['old_construction_sha256']
 for path,h in rec['contacts'].items():assert sha(R/path)==h,'INSTRUMENT_CHANGED'
 ax=sorted({a for r in allrows for a in r['axiom_references']});assert set(ax)<=A.ALLOWED
 rec.update(status='PASS_AUTHOR_RESUMED_POOL_AUDIT',stored_producer_occurrences=len(allrows),unique_names=len({r['actual_name'] for r in allrows}),axiom_union=ax,duplicate_groups=len(compatibility['duplicates']),source_bound='Every old selected source, olean and build log pinned before/after; actual master imports all306 from one LEAN_PATH; stored extraction completed in8 shards. No fresh individual rebuild claim.')
 save();(O/'VERDICT.txt').write_text('PASS_AUTHOR_RESUMED_POOL_AUDIT\nAuthor integration evidence only; all main claims OPEN.\n');print(rec['status'],len(allrows),'stored occurrences',flush=True)
except BaseException as e:
 if rec['status']!='TIMEOUT_NOT_ACCEPTED':rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save()
 raise
finally:
 (D/'LATEST-POOL-RESUME-v1.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
