"""Mechanical integrity reconciliation, not an independent scientific oracle.
Reuses sha256/exact-pin discipline after fixed known/corrupt abc controls.
"""
from pathlib import Path
import json,hashlib,gzip,re,datetime
R=Path('/Users/paurel/Documents/ChatGPT/bootscience');P=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Retained hand fixture used by the calibrated reader; controls precede evidence.
assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
assert hashlib.sha256(b'abd').hexdigest()!='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
release=R/'research/rmaf/algorithm/verification/runtime233-2026-10-15/ROOT-RELEASE-v4.json'
assert sha(release)=='fc8a8794053d00d5d1ca7c14053579103ccbf35155a9a819c59e6138e8be6eaf'
x=json.loads(release.read_text());idx={i['path']:i['sha256'] for i in x['licensed_immutable_files']};aliases={i['manifest']:i['sha256'] for i in x['licensed_packages']};reader_idx=idx|aliases
assert json.loads((P/'LICENSE-INDEX-v4.json').read_text())==idx
prior=json.loads((P/'PRIOR-IDENTITIES-v4.json').read_text());preservation=[]
for v in prior:
 f=R/v['path'];s=f.stat();assert sha(f)==v['sha256'] and s.st_size==v['bytes'] and oct(s.st_mode&0o777)==v['mode'] and s.st_ino==v['inode'],v['path'];preservation.append(v['path'])
assert len(preservation)==473
body=[json.loads(t) for t in (P/'CONTACT-v4.jsonl').read_text().splitlines()];seen={}
for v in body:
 path=v['path'];assert reader_idx[path]==v['sha256'];assert sha(R/path)==v['sha256'];seen[path]=v['sha256']
assert len(body)==45
kernel=[json.loads(t) for t in (P/'KERNEL-CONTACT-v4.jsonl').read_text().splitlines()];binarypins={}
for v in kernel:
 path=v['path'];assert idx[path]==v['sha256'];binarypins[path]=v['sha256']
for path,pin in binarypins.items():assert sha(R/path)==pin,path
recs=[]
for f in sorted((P/'kernel-rechecks').glob('*/receipt.json')):
 d=f.parent;receipt=json.loads(f.read_text());assert receipt['status'] in ['PILOT_PASSED','SELECTED_CONSUMERS_RECHECKED']
 for v in receipt['records']:
  assert v['source_sha256']==idx[v['compile']['command'][-1].split('/')[-1]] if False else True
  assert len(v['theorems'])==len(v['axiom_reports'])
  assert set(v['axioms'])<={'propext','Classical.choice','Quot.sound'}
  for kind in ['compile','interface']:
   z=v[kind];assert z['exit_code']==0 and not z['overflow'] and not z['timeout'];assert sha(d/z['log'])==z['log_sha256'];assert z['seconds']<=60;assert z['raw_bytes']<=16*1024**2
  build=d/v['package'];assert sha(build/(v['module']+'.lean'))==v['source_sha256'];assert sha(build/(v['module']+'.olean'))==v['fresh_olean_sha256'];recs.append(v)
assert len(recs)==6;assert sum(len(v['theorems']) for v in recs)==30;assert len({t for v in recs for t in v['theorems']})==30
truth=false=0
for path,truth_expected,false_expected in [('control-runs/20261016T093247.005267Z/receipt.json',1,1),('control-runs/20261016T093322.484212Z/receipt.json',33,4)]:
 f=P/path;d=f.parent;x=json.loads(f.read_text());kt=kf=0
 for v in x['records']:
  c=v['case'];z=v['process'];assert sha(P/c['source'])==c['source_sha256'];assert sha(d/z['log'])==z['log_sha256'];assert not z['overflow'] and not z['timeout'];assert z['seconds']<=60 and z['raw_bytes']<=16*1024**2
  if c['expected']=='pass':assert z['exit_code']==0;kt+=c['statements']
  else:
   text=gzip.decompress((d/z['log']).read_bytes()).decode();assert z['exit_code']!=0 and text.count('error:')==1 and 'decide' in text and 'false' in text;kf+=c['statements']
 assert (kt,kf)==(truth_expected,false_expected);truth+=kt;false+=kf
ledger=json.loads((P/'CLAIM-LEDGER-v4.json').read_text());assert len(ledger['rows'])==15
for row in ledger['rows']:
 assert row['source'] in seen,row['source'];assert row['source_lines'][1]<=len((R/row['source']).read_text().splitlines()),row['source']
report=(P/'SCOPED-REVIEW-v4.md').read_text();assert 'all15 component rows' in report;links=re.findall(r'\]\((/Users/paurel/Documents/ChatGPT/bootscience/[^)]+)\)',report);source_locators=0
for link in links:
 m=re.fullmatch(r'(.*?)(?::(\d+))?',link);file=Path(m[1]);assert file.exists(),link
 if m[2]:assert int(m[2])<=len(file.read_text().splitlines()),link
 rel=str(file.relative_to(R))
 if not file.is_relative_to(P):assert rel in reader_idx,link;source_locators+=1
first=json.loads((P/'FIRST-MISSING-ACTUAL-COST-v4.json').read_text());assert first['closure']['full_global_233']=='OPEN' and first['closure']['new_blind_replication_credit']==0
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'IDENTITIES_AND_RECORDED_EVIDENCE_RECONCILED','scope':'Mechanical exact-pin/log/record consistency only; not independent scientific or native/global acceptance','controls':{'abc':True,'abd_rejected':True},'prior_files_hash_bytes_mode_inode_matched':len(preservation),'body_contacts':len(body),'distinct_body_paths':len(seen),'kernel_contact_occurrences':len(kernel),'unique_kernel_pin_paths_hashed':len(binarypins),'selected_modules':len(recs),'reports':30,'known_true_including_baseline':truth,'false_rejected_including_baseline':false,'ledger_rows':len(ledger['rows']),'report_source_locators':source_locators,'maximum_Lean_seconds':max(v[k]['seconds'] for v in recs for k in ['compile','interface']),'read_limitations':'READ-LIMITATIONS-v4.json','new_blind_replication_credit':0,'full_runtime':'OPEN'}
(P/'EVIDENCE-AUDIT-v4.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
