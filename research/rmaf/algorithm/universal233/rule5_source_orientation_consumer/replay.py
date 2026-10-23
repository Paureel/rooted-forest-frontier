#!/usr/bin/env python3
"""One-shot bounded author replay; existing DEVELOPMENT producer audit reused.
The toolkit has no rooted-tree consumer instrument. Wrap the completed audit
with exact source isolation and bounded compressed output, without changing it.
"""
from pathlib import Path
import datetime,gzip,hashlib,importlib.util,json,os,re,selectors,shutil,subprocess,sys,time
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;R=D.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def margin():
 if shutil.disk_usage(D).free<2*1024**3:raise RuntimeError('DISK_MARGIN_UNDER_2_GIB')
margin()
rel=json.loads((D/'STRUCTURAL-INPUT-RELEASE-v1.json').read_text());M=R/rel['manifest'];pin(M,rel['sha256']);manifest=json.loads(M.read_text())
for e in manifest['immutable_files']:pin(R/e['snapshot'],e['sha256'])
F=M.parent;S=F/'results/algorithm-universal233-rule5-final-classification-replay-20261015T145040Z'
prior=json.loads((S/'certificate.json').read_text());assert prior['status']=='PASS_AUTHOR_KERNEL_OPEN'
A=F/'research/rmaf/algorithm/universal233/rule5_final_classification/audit.py'
spec=importlib.util.spec_from_file_location('completed_development_audit',A);audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit);audit.R=R
pre=json.loads((D/'PRODUCER-PREFLIGHT-v1.json').read_text());P=R/pre['manifest'];pin(P,pre['sha256']);pc=json.loads(P.read_text());assert pc['status']=='PASS_AUTHOR_PRODUCER_PREFLIGHT';assert pc['instrument_sha256']==sha(A)
for e in pc['immutable_files']:pin(R/e['path'],e['sha256']);assert not (R/e['path']).stat().st_mode&0o222
# Clean/corrupted foreign-path twins precede candidate source application.
C=P.parent;clean=next(C.glob('CleanAudit-*.log')).read_text();audit.parse(clean,['CleanA','CleanB'],C)
bad=clean.replace('PATH|CleanA|'+str(C/'CleanA.olean'),'PATH|CleanA|/tmp/foreign/CleanA.olean',1)
try:audit.parse(bad,['CleanA','CleanB'],C)
except AssertionError:foreign='CAUGHT'
else:raise AssertionError('FOREIGN_PATH_CORRUPTION_SURVIVED')
O=R/'results'/('algorithm-universal233-rule5-source-orientation-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir();(O/'lean-toolchain').write_bytes((S/'lean-toolchain').read_bytes())
new=['UnorderedExchange','SourceTransport323','SourceTransport321','SelectedExchange','SelectedConsumers','RecursiveConsumers','OrientationControls','ConsumerControls'];mods=[e['module'] for e in prior['source_entries']]+new
assert len(mods)==len(set(mods))
record={'status':'RUNNING_AUTHOR','independent_credit':0,'main_milestones':'ALL_OPEN','structural_input_release':rel,'producer_preflight':pre,'audit_sha256':sha(A),'source_entries':[],'runs':[],'controls':{'foreign_path':foreign},'disk_minimum_free_bytes':2*1024**3,'module_timeout_seconds':30,'producer_output_cap_bytes':40*1024**2,'input_hashes':{}}
def save():(O/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
for n in mods:
 p=(S if n not in new else D)/(n+'.lean');src=p.read_bytes();clean_src=re.sub(rb'--[^\n]*',b'',re.sub(rb'/\-.*?\-/',b'',src,flags=re.S));assert not re.search(rb'\b(sorry|admit|axiom|native_decide)\b',clean_src),n
 (O/(n+'.lean')).write_bytes(src);record['source_entries'].append({'module':n,'source':str(p.relative_to(R)),'sha256':sha(p)})
for n in ['OrientationFalseControls','ConsumerFalseControls']:(O/(n+'.lean')).write_bytes((D/(n+'.lean')).read_bytes())
for n in ['CONTROLS-PIN-v1.md','TARGET-v1.md','README.md','FIRST-GAP-v1.md','replay.py','dev.py']:
 p=D/n;record['input_hashes'][str(p.relative_to(R))]=sha(p);(O/n).write_bytes(p.read_bytes())
save()
def run(n,build=False,want=0,cap=3*1024**2):
 margin();start=time.monotonic();cmd=[str(R/'bootloops-lean')]+(['-o',str(O/(n+'.olean'))] if build else [])+[str(O/(n+'.lean'))]
 p=subprocess.Popen(cmd,cwd=O,env=dict(os.environ,LEAN_PATH=str(O)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT);sel=selectors.DefaultSelector();sel.register(p.stdout,selectors.EVENT_READ);count=0;failed=None
 with gzip.open(O/(n+'.log.gz'),'wb') as f:
  while sel.get_map():
   if time.monotonic()-start>30:failed='MODULE_TIMEOUT';p.kill()
   for key,_ in sel.select(.2):
    chunk=os.read(key.fileobj.fileno(),65536)
    if not chunk:sel.unregister(key.fileobj);continue
    count+=len(chunk)
    if count>cap:failed='OUTPUT_CAP';p.kill()
    if count<=cap:f.write(chunk)
   if failed and p.poll() is not None:break
 p.wait();sel.close();row={'module':n,'exit':p.returncode,'seconds':time.monotonic()-start,'uncompressed_output_bytes':count,'compressed_output_bytes':(O/(n+'.log.gz')).stat().st_size,'failure':failed};record['runs'].append(row);save();print(n,p.returncode,round(row['seconds'],3),flush=True)
 if failed or p.returncode!=want:raise AssertionError(row)
 with gzip.open(O/(n+'.log.gz'),'rt') as f:txt=f.read(cap+1)
 assert len(txt)<=cap
 return txt
try:
 for n,text,want in [('StdTrue','import Std\nexample : (3:Nat)+4=7 := by decide\n',0),('StdFalse','import Std\nexample : (3:Nat)+4=8 := by decide\n',1)]:
  (O/(n+'.lean')).write_text(text);out=run(n,want=want)
  if want:assert out.count('is false')==1
 for n in mods:run(n,True)
 for n,count in [('OrientationFalseControls',3),('ConsumerFalseControls',6)]:
  out=run(n,want=1);assert out.count('is false')==count;record['controls'][n]={'mathematical_rejections':count};save()
 (O/'ProducerAudit.lean').write_text(audit.audit_source(mods));out=run('ProducerAudit',cap=40*1024**2);rows,summaries,paths=audit.parse(out,mods,O)
 required=['Universal233.Rule5SourceOrientation.'+n for n in ['selected_base','selected_first_cover','selected_third_cover','first_child_solver','third_child_solver','selected_child_states','selected_original_endpoint_cuts']]
 for key in required:assert any(r['name']==key for r in rows),key
 for tag,bad in [('missing_occurrence',re.sub(r'^PRODUCERJSON\|.*\n','',out,count=1,flags=re.M)),('duplicate_occurrence',out+'PRODUCERJSON|'+json.dumps(rows[0])+'\n')]:
  try:audit.parse(bad,mods,O)
  except AssertionError:record['controls'][tag]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
 for e in record['source_entries']:pin(R/e['source'],e['sha256']);pin(O/(e['module']+'.lean'),e['sha256'])
 for p,h in record['input_hashes'].items():pin(R/p,h)
 for e in manifest['immutable_files']:pin(R/e['snapshot'],e['sha256'])
 with gzip.open(O/'producer-occurrences.json.gz','wt') as f:json.dump(rows,f,separators=(',',':'))
 record.update(status='PASS_AUTHOR_SOURCE_ORIENTATION_CONSUMERS_OPEN',source_builds=len(mods),stored_producer_occurrences=len(rows),axiom_union=sorted({a for r in rows for a in r['axiom_references']}),interfaces=required,completed_author_scope=['actual selected Figure15.1 and Figure15.3 covers','all source fork/endpoint/cut orders','target InRegion cluster and root sides','executable selected endpoint nonrefusal','actual cuts/partitions/source states/[1,2] budgets/individual child IHs'],first_unprovided_full_rule_call='parent recursive dispatcher joining .one/.first/.second/.third with actual local IHs',skipped=['toolkit-wide suite','large census','paid Figure15.2 surgery','parent/reviewer unfinished sources','fresh nonauthor semantic/interface/prose review','full algorithm/base/novelty acceptance'])
 save();(O/'VERDICT.txt').write_text(record['status']+'\nAuthor kernel source replay only; main algorithm milestones and independent acceptance remain OPEN.\n');(D/'LATEST-REPLAY-v1.json').write_text(json.dumps({'receipt':str(O.relative_to(R)),'sha256':sha(O/'certificate.json')},indent=2)+'\n');print(record['status'],len(mods),'modules;',len(rows),'stored occurrences;',O,flush=True)
except BaseException as e:
 record['status']='FAILED_AUTHOR_REPLAY';record['error']=repr(e);save();raise
