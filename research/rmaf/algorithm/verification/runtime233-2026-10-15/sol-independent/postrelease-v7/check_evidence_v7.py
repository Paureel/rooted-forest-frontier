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
release=R/'research/rmaf/algorithm/verification/runtime233-2026-10-15/ROOT-RELEASE-v7.json'
assert sha(release)=='ddf2e1e81352d367c8f551b45a6e74972b9da968380f1bbbd30c4ed9dfc6208c'
x=json.loads(release.read_text());idx={i['path']:i['sha256'] for i in x['licensed_immutable_files']};aliases={i['manifest']:i['sha256'] for i in x['licensed_packages']};reader_idx=idx|aliases
assert json.loads((P/'LICENSE-INDEX-v7.json').read_text())==idx
prior=json.loads((P/'PRIOR-IDENTITIES-v7.json').read_text());preservation=[]
for path,v in prior.items():
 f=R/path;s=f.stat();assert sha(f)==v['sha256'] and s.st_size==v['bytes'] and oct(s.st_mode&0o777)==v['mode'] and s.st_ino==v['inode'],path;preservation.append(path)
assert len(preservation)==1022
body=[json.loads(t) for t in (P/'CONTACT-v7.jsonl').read_text().splitlines()];seen={}
for v in body:
 path=v['path'];assert reader_idx[path]==v['sha256'];assert sha(R/path)==v['sha256'];seen[path]=v['sha256']
assert len(body)==77
kernel=[json.loads(t) for t in (P/'KERNEL-CONTACT-v7.jsonl').read_text().splitlines()];binarypins={}
for v in kernel:
 path=v['path'];assert idx[path]==v['sha256'];binarypins[path]=v['sha256']
for path,pin in binarypins.items():assert sha(R/path)==pin,path
recs=[]
for f in sorted((P/'kernel-rechecks').glob('*/receipt.json')):
 d=f.parent;receipt=json.loads(f.read_text());assert receipt['status'] in ['PILOT_PASSED','SELECTED_CONSUMERS_RECHECKED']
 for v in receipt['records']:
  planned=next(i for i in json.loads((P/'RECHECK-PLAN-v7.json').read_text())['modules'] if i['package']==v['package']);assert v['source_sha256']==planned['source_sha256']==idx[planned['source']];assert sha(R/planned['source'])==planned['source_sha256']
  assert len(v['theorems'])==len(v['axiom_reports'])
  assert set(v['axioms'])<={'propext','Classical.choice','Quot.sound'}
  for kind in ['compile','interface']:
   z=v[kind];assert z['exit_code']==0 and not z['overflow'] and not z['timeout'];assert sha(d/z['log'])==z['log_sha256'];assert z['seconds']<=60;assert z['raw_bytes']<=16*1024**2
  build=d/v['package'];assert sha(build/(v['module']+'.lean'))==v['source_sha256'];assert sha(build/(v['module']+'.olean'))==v['fresh_olean_sha256'];recs.append(v)
assert len(recs)==37;assert sum(len(v['theorems']) for v in recs)==90;assert len({t for v in recs for t in v['theorems']})==90
truth=false=0
control_summary=json.loads((P/'OWN-CONTROL-RESULTS-v7.json').read_text())
assert control_summary['new_true']==41 and control_summary['new_false_rejected']==7
for v in control_summary['records']:
 c=v['case'];z=v['process'];assert sha(P/c['source'])==c['source_sha256']
 d=Path(z['cwd']);assert d.is_relative_to(P);assert sha(d/z['log'])==z['log_sha256'];assert not z['overflow'] and not z['timeout'];assert z['seconds']<=60 and z['raw_bytes']<=16*1024**2
 if c['expected']=='pass':assert z['exit_code']==0;truth+=c['statements']
 else:
  printed=gzip.decompress((d/z['log']).read_bytes()).decode();assert z['exit_code']!=0 and printed.count('error:')==1 and 'decide' in printed and 'false' in printed;false+=c['statements']
assert (truth,false)==(42,8)
for v in control_summary['sources']:
 assert sha(P/v['path'])==v['sha256']
for f in (P/'control-runs').glob('*/plan.source.json'):
 pl=json.loads(f.read_text());assert sha(P/pl['fixture'])==pl['fixture_sha256']
 for v in pl['items']:assert sha(P/v['source'])==v['source_sha256']
ledger=json.loads((P/'CLAIM-LEDGER-v7.json').read_text());assert len(ledger['rows'])==28
for row in ledger['rows']:
 assert row['source'] in seen,row['source'];assert row['source_lines'][1]<=len((R/row['source']).read_text().splitlines()),row['source']
report=(P/'SCOPED-REVIEW-v7.md').read_text();assert 'all 28 reviewed rows' in report;links=re.findall(r'\]\((/Users/paurel/Documents/ChatGPT/bootscience/[^)]+)\)',report);source_locators=0
for link in links:
 m=re.fullmatch(r'(.*?)(?::(\d+))?',link);file=Path(m[1]);assert file.exists(),link
 if m[2]:assert int(m[2])<=len(file.read_text().splitlines()),link
 rel=str(file.relative_to(R))
 if not file.is_relative_to(P):assert rel in reader_idx,link;source_locators+=1
first=json.loads((P/'FIRST-MISSING-ACTUAL-COST-v7.json').read_text());assert first['closure']['complete_abstract_bit_233']=='OPEN' and first['closure']['new_blind_replication_credit']==0
plan=json.loads((P/'RECHECK-PLAN-v7.json').read_text())
for rel,pin in plan['own_prerequisite_pins'].items():assert sha(R/rel)==pin
old=P.parent/'postrelease-v6';clean=json.loads((R/plan['own_prerequisite_receipt']).read_text())
for rel,pin in clean['own_import_pins'].items():assert sha(old/rel)==pin
original=R/clean['original_source'];assert sha(original)==clean['original_sha256'];own=old/'clean-import/OWBudgets.lean';assert own.read_text().splitlines()[0]=='import OWOptimize';assert own.read_text().splitlines()[1:]==original.read_text().splitlines()[1:]
assert len(clean['axiom_reports'])==2 and set(clean['axioms'])<={'propext','Classical.choice','Quot.sound'}
for kind in ['compile','interface']:
 z=clean[kind];assert z['exit_code']==0 and not z['overflow'] and not z['timeout'];assert sha(old/clean['logs_relative_directory']/z['log'])==z['log_sha256']
assert sum(f.stat().st_size for f in P.rglob('*') if f.is_file())<256*1024**2
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'IDENTITIES_AND_RECORDED_EVIDENCE_RECONCILED','scope':'Mechanical exact-pin/log/record consistency only; not independent scientific or native/global acceptance','controls':{'abc':True,'abd_rejected':True},'prior_files_hash_bytes_mode_inode_matched':len(preservation),'body_contacts':len(body),'distinct_body_paths':len(seen),'kernel_contact_occurrences':len(kernel),'unique_kernel_pin_paths_hashed':len(binarypins),'selected_modules':len(recs),'reports':90,'known_true_including_baseline':truth,'false_rejected_including_baseline':false,'ledger_rows':len(ledger['rows']),'report_source_locators':source_locators,'maximum_Lean_seconds':max(v[k]['seconds'] for v in recs for k in ['compile','interface']),'read_limitations':'READ-LIMITATIONS-v7.json','new_blind_replication_credit':0,'full_runtime':'OPEN'}
(P/'EVIDENCE-AUDIT-v7.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
