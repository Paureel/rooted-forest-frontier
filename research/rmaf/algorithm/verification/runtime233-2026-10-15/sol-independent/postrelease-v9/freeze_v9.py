"""Reuse calibrated own-manifest freeze; no scientific computation or author code."""
from pathlib import Path
import datetime,hashlib,json,stat,shutil
P=Path(__file__).resolve().parent;R=Path('/Users/paurel/Documents/ChatGPT/bootscience')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert shutil.disk_usage(P).free>=3*1024**3
prior=json.loads((P/'PRIOR-IDENTITIES-v9.json').read_text())
for rel,x in prior.items():
 p=R/rel;s=p.stat();assert sha(p)==x['sha256'] and s.st_size==x['bytes'] and oct(stat.S_IMODE(s.st_mode))==x['mode'] and s.st_ino==x['inode'],rel
assert len(prior)==1658
fin=json.loads((P/'FINALIZATION-v9.json').read_text())
for key in ['primary_report','claim_ledger','exact_remaining_premises','mechanical_evidence_audit','control_results','import_correction','prose_check']:
 x=fin[key];assert sha(P/x['path'])==x['sha256'],key
skip={'FINAL-MANIFEST-v9.json','FINAL-MANIFEST-v9.sha256'}
files=sorted(p for p in P.rglob('*') if p.is_file() and str(p.relative_to(P)) not in skip)
assert not any(p.is_symlink() for p in P.rglob('*'))
assert sum(p.stat().st_size for p in files)<256*1024**2
for p in files:p.chmod(0o444)
art={str(p.relative_to(P)):{'sha256':sha(p),'bytes':p.stat().st_size,'mode':oct(stat.S_IMODE(p.stat().st_mode))} for p in files}
m=dict(version=9,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='FROZEN_SOURCE_REPRESENTED_LOCAL_SCOPE_QUALIFIED_SURVIVAL',no_further_writes=True,release={'path':'research/rmaf/algorithm/verification/runtime233-2026-10-15/ROOT-RELEASE-v9.json','sha256':'775fc4dd1ca858d6cd0e9796f08aa959b8427d29f3737770d96687e5d4eb783f'},paths_relative_to='this manifest directory',payload_count=len(art),payload_bytes=sum(x['bytes'] for x in art.values()),prior_files_preserved=len(prior),selected_source_rechecks=36,actual_type_axiom_reports=95,retained_all_source_rechecks=40,retained_all_type_axiom_reports=111,new_true_controls=32,new_true_finite_decide=31,new_true_public_source_value_proof=1,new_false_controls=7,reviewed_rows=25,new_blind_replication_credit=0,full_W_w='OPEN',full_abstract_bit_233='OPEN',full_recovery_bit_execution='OPEN',native_compiler_heap='OPEN',independent_functional='OPEN',novelty='OPEN',qualification='Final36/95 evidence uses32 original nonglobal and4 corrected global rechecks; original4 global shadow-context rechecks/control runs retained but excluded. Own v6 import-only OWBudgets adapter first, own thin copies of11exact licensed global/Rule4 payloads; excludes author global/Rule4 roots with unlicensed shadow hardlinks. Same-lineage imported body/origin/initializer/control-namespace and author theorem-text/object-bridge qualifications remain. No author auditor/oracle/control SOURCE or PROGRAM explicitly compiled/invoked, no full W/w/bit/native or new independence.',report=fin['primary_report']['path'],ledger=fin['claim_ledger']['path'],first_gap=fin['exact_remaining_premises']['path'],import_correction=fin['import_correction']['path'],artifacts=art)
out=P/'FINAL-MANIFEST-v9.json';out.write_text(json.dumps(m,indent=2)+'\n');pin=sha(out)
(P/'FINAL-MANIFEST-v9.sha256').write_text(pin+'  FINAL-MANIFEST-v9.json\n')
out.chmod(0o444);(P/'FINAL-MANIFEST-v9.sha256').chmod(0o444)
for d in sorted((d for d in P.rglob('*') if d.is_dir()),key=lambda p:len(p.parts),reverse=True):d.chmod(0o555)
P.chmod(0o555)
for rel,x in art.items():
 p=P/rel;assert sha(p)==x['sha256'] and p.stat().st_size==x['bytes'] and stat.S_IMODE(p.stat().st_mode)==0o444,rel
assert sha(out)==pin
for rel,x in prior.items():
 p=R/rel;s=p.stat();assert sha(p)==x['sha256'] and s.st_size==x['bytes'] and oct(stat.S_IMODE(s.st_mode))==x['mode'] and s.st_ino==x['inode'],rel
print(json.dumps(dict(status='FROZEN_AND_SELF_MATCHED',manifest=str(out),manifest_sha256=pin,payload_count=len(art),payload_bytes=m['payload_bytes'],report=fin['primary_report']['path'],report_sha256=sha(P/m['report']),prior_files_preserved=len(prior),final_source_modules=36,final_reports=95,new_true=32,new_false=7,ledger_rows=25,new_blind_replication_credit=0,full_W_w='OPEN',full_abstract_bit_233='OPEN',native='OPEN'),indent=2))
