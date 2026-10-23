#!/usr/bin/env python3
"""One-shot exact source union replay and bounded compact producer audit.
Reuse the completed source inventories and local instrument; no raw pool
records copied. All author contacts DEVELOPMENT, no independent acceptance.
"""
from pathlib import Path
import datetime,gzip,hashlib,json,re,shutil,sys
sys.dont_write_bytecode=True
import instrument,pilot
D=Path(__file__).resolve().parent;R=D.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def compat(rows):
 seen={}
 for r in rows:
  key=(r['kind'],r['type'],r['body'] if r['kind']!='theorem' else None)
  if r['name'] in seen:assert seen[r['name']]==key,'COALESCED_TYPE_NONPROOF_BODY_MISMATCH'
  else:seen[r['name']]=key
 return len(seen)
# Fresh literal compatibility clean/corrupt twins precede scientific rows.
plant={'name':'literal','kind':'definition','type':'Nat','body':'3'}
assert compat([plant,dict(plant)])==1
try:compat([plant,dict(plant,body='4')])
except AssertionError:body_control='CAUGHT'
else:raise AssertionError('BODY_CORRUPTION_SURVIVED')
try:compat([plant,dict(plant,type='Bool')])
except AssertionError:type_control='CAUGHT'
else:raise AssertionError('TYPE_CORRUPTION_SURVIVED')
U=D/'SOURCE-UNION-v1.json';union=json.loads(U.read_text());assert union['status']=='PASS_EXACT_DEVELOPMENT_SOURCE_UNION'
P=json.loads((D/'PRODUCER-PREFLIGHT-v1.json').read_text());M=R/P['manifest'];pin(M,P['sha256']);pre=json.loads(M.read_text());assert pre['status']=='PASS_FRESH_STD_PRODUCER_CONTROLS';pin(D/'instrument.py',pre['instrument_sha256'])
for e in pre['immutable_files']:pin(R/e['path'],e['sha256'])
O=R/'results'/('algorithm-universal233-rule5-common-selector-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir();(O/'lean-toolchain').write_bytes((D/'build/lean-toolchain').read_bytes())
entries=list(union['modules'])
for n in ['CommonInterfaces','CommonConsumer','CommonControls']:entries.append({'module':n,'source':str((D/(n+'.lean')).relative_to(R)),'source_sha256':sha(D/(n+'.lean')),'sha256':sha(D/(n+'.lean')),'adaptations':{},'origin':'new_author_consumer'})
mods=[e['module'] for e in entries];assert len(mods)==len(set(mods))==315
record={'status':'RUNNING_AUTHOR','independent_credit':0,'main_milestones':'ALL_OPEN','source_union_sha256':sha(U),'source_entries':entries,'producer_preflight':P,'controls':{'nonproof_body_corruption':body_control,'type_corruption':type_control},'runs':[],'producer_shards':[],'input_hashes':{},'module_timeout_seconds':30,'perproducer_uncompressed_cap':8*1024**2,'cumulative_producer_cap':256*1024**2,'disk_floor_bytes':3*1024**3}
def save():(O/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
for e in entries:
 p=R/e['source'];pin(p,e['source_sha256']);s=p.read_text()
 for a,z in e['adaptations'].items():s=re.sub(r'(?m)^import '+re.escape(a)+r'$',lambda _:'import '+z,s)
 assert hashlib.sha256(s.encode()).hexdigest()==e['sha256'];(O/(e['module']+'.lean')).write_text(s)
 clean=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S));assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean),e['module']
 for imp in re.findall(r'(?m)^import (\w+)$',s):assert imp in mods or imp in ['Std','Lean'],'UNDECLARED_IMPORT|'+imp
for n in ['CommonFalseControls']:(O/(n+'.lean')).write_bytes((D/(n+'.lean')).read_bytes())
for n in ['README.md','TARGET-v1.md','FIRST-GAP-v1.md','GUARD-LEDGER-v1.md','AUDIT-SCOPE-v1.md','CONTROLS-PIN-v1.md','replay.py','instrument.py','pilot.py','SOURCE-UNION-v1.json']:
 p=D/n;record['input_hashes'][str(p.relative_to(R))]=sha(p);(O/n).write_bytes(p.read_bytes())
save()
def run(n,build=False,want=0):
 before=set(O.glob(n+'-*.log.gz'));out=pilot.run(O,n,build,want);log=next(iter(set(O.glob(n+'-*.log.gz'))-before));record['runs'].append({'module':n,'exit_expected':want,'log':str(log.relative_to(R)),'sha256':sha(log)});save();return out
try:
 for n,text,want in [('StdTrue','import Std\nexample : (3:Nat)+4=7 := by decide\n',0),('StdFalse','import Std\nexample : (3:Nat)+4=8 := by decide\n',1)]:
  (O/(n+'.lean')).write_text(text);s=run(n,want=want)
  if want:assert s.count('is false')==1
 for n in mods:run(n,True)
 s=run('CommonFalseControls',want=1);assert s.count('is false')==6;record['controls']['mathematical_false_rejections']=6
 (O/'CommonMaster.lean').write_text('\n'.join('import '+n for n in mods)+'\n');run('CommonMaster',True)
 allrows=[];total=0
 for i in range(0,len(mods),8):
  wanted=mods[i:i+8];F=O/('records-'+str(i//8));F.mkdir();n='ProducerAudit'+str(i//8);(O/(n+'.lean')).write_text(instrument.source(['CommonMaster'],wanted,F));run(n)
  rows=instrument.parse(F,wanted,O);allrows+=rows
  size=sum(p.stat().st_size for p in F.glob('*.json.gz'));total+=size
  assert total<=256*1024**2,'CUMULATIVE_OUTPUT_CAP'
  record['producer_shards'].append({'producers':wanted,'occurrences':len(rows),'compressed_bytes':size,'files':[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in sorted(F.iterdir())]});save()
 resolved=compat(allrows);required=['Universal233.Rule5CommonSelector.'+n for n in ['vertices_exact','incident_exact','selected_common_checks','selected_original_source','selected_one_nonrefusal','selected_one_bounded_solver','selected_one_job_progress']]
 for n in required:assert any(r['name']==n for r in allrows),n
 for e in entries:pin(R/e['source'],e['source_sha256']);pin(O/(e['module']+'.lean'),e['sha256'])
 for p,h in record['input_hashes'].items():pin(R/p,h)
 record.update(status='PASS_AUTHOR_ACTUAL_ONE_SOURCE_CONSUMER_OPEN',source_builds=len(mods),stored_producer_occurrences=len(allrows),resolved_unique_names=resolved,axiom_union=sorted({a for r in allrows for a in r['axiom_references']}),interfaces=required,producer_output_compressed_bytes=total,audit_scope='Theorem proof text omitted; actual stored ConstantInfo proof/body references and AX closure retained; every nonproof/opaque body retained full.',first_unprovided_main_call='parent total dispatcher/current-budget binding/bit-payload recurrence',skipped=['toolkit-wide suite','large census','fresh nonauthor semantic/interface/prose review','main algorithm/base/novelty acceptance'])
 save();(O/'VERDICT.txt').write_text(record['status']+'\nAuthor source/AX evidence only; independent acceptance and all main milestones OPEN.\n');(D/'LATEST-REPLAY-v1.json').write_text(json.dumps({'receipt':str(O.relative_to(R)),'sha256':sha(O/'certificate.json')},indent=2)+'\n');print(record['status'],len(mods),'modules',len(allrows),'stored occurrences',total,'compressed bytes',O,flush=True)
except BaseException as e:record['status']='FAILED_AUTHOR_SOURCE_REPLAY';record['error']=repr(e);save();raise
