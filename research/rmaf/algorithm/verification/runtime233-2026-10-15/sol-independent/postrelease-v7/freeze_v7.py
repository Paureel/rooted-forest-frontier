"""Freeze only the new own phase7 after complete scoped evidence reconciliation."""
from pathlib import Path
import datetime,hashlib,json,stat,shutil
P=Path(__file__).resolve().parent;R=Path('/Users/paurel/Documents/ChatGPT/bootscience')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert shutil.disk_usage(P).free>=3*1024**3
prior=json.loads((P/'PRIOR-IDENTITIES-v7.json').read_text())
for rel,x in prior.items():
 p=R/rel;s=p.stat();assert sha(p)==x['sha256'] and s.st_size==x['bytes'] and oct(stat.S_IMODE(s.st_mode))==x['mode'] and s.st_ino==x['inode'],rel
assert len(prior)==1022
fin=json.loads((P/'FINALIZATION-v7.json').read_text())
for key in ['primary_report','claim_ledger','exact_remaining_premises','mechanical_evidence_audit']:
 x=fin[key];assert sha(P/x['path'])==x['sha256'],key
skip={'FINAL-MANIFEST-v7.json','FINAL-MANIFEST-v7.sha256'}
files=sorted(p for p in P.rglob('*') if p.is_file() and str(p.relative_to(P)) not in skip)
assert not any(p.is_symlink() for p in P.rglob('*'))
assert sum(p.stat().st_size for p in files)<256*1024**2
for p in files:p.chmod(0o444)
art={str(p.relative_to(P)):{'sha256':sha(p),'bytes':p.stat().st_size,'mode':oct(stat.S_IMODE(p.stat().st_mode))} for p in files}
m={'version':7,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_SOURCE_REFERENCE_SCOPE_QUALIFIED_SURVIVAL','no_further_writes':True,'release':{'path':'research/rmaf/algorithm/verification/runtime233-2026-10-15/ROOT-RELEASE-v7.json','sha256':'ddf2e1e81352d367c8f551b45a6e74972b9da968380f1bbbd30c4ed9dfc6208c'},'paths_relative_to':'this manifest directory','payload_count':len(art),'payload_bytes':sum(x['bytes'] for x in art.values()),'prior_files_preserved':1022,'selected_source_rechecks':37,'actual_type_axiom_reports':90,'new_true_controls':41,'new_false_controls':7,'reviewed_rows':28,'new_blind_replication_credit':0,'full_W_w':'OPEN','full_abstract_bit_233':'OPEN','full_recovery_bit_execution':'OPEN','native_compiler_heap':'OPEN','qualification':'Exact selected-source compiler/kernel rechecks in named same-lineage contexts only. Imported body/origin/initializer closure not audited. Old own import-only OWBudgets adapter and v6.1 correction reused. Prebuilt proof/control namespaces may load; no author auditor/oracle/control SOURCE or PROGRAM explicitly compiled/invoked. No full W/w or native/global acceptance.','report':'SCOPED-REVIEW-v7.md','ledger':'CLAIM-LEDGER-v7.json','first_gap':'FIRST-MISSING-ACTUAL-COST-v7.json','artifacts':art}
out=P/'FINAL-MANIFEST-v7.json';out.write_text(json.dumps(m,indent=2)+'\n');pin=sha(out)
(P/'FINAL-MANIFEST-v7.sha256').write_text(pin+'  FINAL-MANIFEST-v7.json\n')
out.chmod(0o444);(P/'FINAL-MANIFEST-v7.sha256').chmod(0o444)
for d in sorted((d for d in P.rglob('*') if d.is_dir()),key=lambda p:len(p.parts),reverse=True):d.chmod(0o555)
P.chmod(0o555)
for rel,x in art.items():
 p=P/rel;assert sha(p)==x['sha256'] and p.stat().st_size==x['bytes'] and stat.S_IMODE(p.stat().st_mode)==0o444,rel
assert sha(out)==pin
print(json.dumps({'status':'FROZEN_AND_SELF_MATCHED','manifest':str(out),'manifest_sha256':pin,'payload_count':len(art),'payload_bytes':m['payload_bytes'],'report_sha256':sha(P/m['report']),'prior_files_preserved':len(prior),'source_modules':37,'reports':90,'new_true':41,'new_false':7,'ledger_rows':28,'new_blind_replication_credit':0,'complete_full_W_w':'OPEN','complete_abstract_bit_233':'OPEN','native':'OPEN'},indent=2))
