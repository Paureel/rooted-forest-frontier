# Readonly source-stage seal; preserves every old freeze and original source mode/inode.
from pathlib import Path
import datetime,gzip,hashlib,json,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
T=R/'research/rmaf/monitoring/global-next-20261016T092805Z/GLOBAL-INTEGRATION-TARGET-v1.json';assert sha(T)=='0b64f4c7cb866f1927f96bf9a0847bf99bf0e981e5f2edeee1b3dabf5158eb23';t=json.loads(T.read_text())
B=R/json.loads((D/'BUILD-v1.json').read_text())['directory'];C=B/'author-audit-v2/certificate.json';c=json.loads(C.read_text())
assert c['status']=='PASS_AUTHOR_ORDINARY_CHILDREN_FOREST_DEBIT_WEIGHTED_SOURCE_INTEGRATION'
assert c['full_proof_body_modules']==6 and len(c['version_compatibility'])==21
assert c['axiom_union']==['Classical.choice','Quot.sound','propext']
for p,h in c['inputs'].items():assert sha(R/p)==h
for e in c['sources']:assert sha(B/(e['module']+'.lean'))==e['source_sha256'] and sha(B/(e['module']+'.olean'))==e['olean_sha256']
previous=[]
for k in ['weighted_prefix_common_agreement','selected_rule5_forest_arms']:
 e=t['allowed_packages'][k];p=R/e['manifest'];assert sha(p)==e['sha256'];m=json.loads(p.read_text());count=0
 for f in m['immutable_files']:
  assert sha(R/f['path'])==f['sha256'];count+=1
 for f in m.get('original_development_sources',[]):
  q=R/f['path'];s=q.stat();assert sha(q)==f['sha256'] and oct(s.st_mode&0o777)==f['mode'] and s.st_ino==f['inode']
 for f in m.get('source_identity',[]):
  q=R/f['path'];s=q.stat();assert sha(q)==f['sha256'] and s.st_mode==f['mode'] and s.st_ino==f['inode']
 previous.append(dict(package=k,manifest=e['manifest'],sha256=e['sha256'],immutable_pins=count,original_source_modes_inodes_preserved=True))
names={'ordinary_run_children_value','ordinary_run_children_local','branchesMeter_value','branchesMeter_work',
 'runChildrenSource_value','children_recursive_debit','childForestDebit_split','runChildrenSource_split',
 'oneSource_value','highSource_value','oneSource_split','highSource_split',
 'sourceSubtotal_eq','sourceSubtotal_bound','simpleBudget_mono','childForestDebit_local_bound',
 'oneSource_local_exponential','highSource_local_exponential','simpleLocalDebit_bound','simpleTreeSource_bound','prefixAndSimpleTreeSource_bound',
 'selected_arm_closed_checker','selectedArmSource_value','selectedArmSource_split','selectedArmSource_local',
 'rule4PartitionMeter_value','rule4BranchesMeter_value','rule4StateMeter_value','rule4Source_value','rule4AnswersSource_split','rule4Source_split'}
interfaces=[]
for e in c['new_producers']:
 if not e['full_proof_bodies']:continue
 p=R/e['path'];assert sha(p)==e['sha256']
 with gzip.open(p,'rt') as f:rows=json.load(f)
 for r in rows:
  short=r['actual_name'].split('.')[-1]
  if short in names:
   assert r['has_body'] and r['body_text_scope']=='FULL_ALL_BODY' and r['body']!='<none>'
   src=B/(e['module']+'.lean');s=src.read_text();match=re.search(r'^.*theorem '+re.escape(short)+r'\b',s,re.M);assert match
   interfaces.append(dict(name=r['actual_name'],module=e['module'],source=str(src.relative_to(R)),line=s[:match.start()].count('\n')+1,type_sha256=hashlib.sha256(r['type'].encode()).hexdigest(),body_sha256=hashlib.sha256(r['body'].encode()).hexdigest(),body_bytes=len(r['body']),axioms=r['axiom_references'],record=e['path'],record_sha256=e['sha256']))
assert {e['name'].split('.')[-1] for e in interfaces}==names
(D/'INTERFACE-TRACE-v1.json').write_text(json.dumps(dict(version=1,status='AUTHOR_SCOPED_SOURCE_INTERFACES_REVIEW_PENDING',canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),interfaces=interfaces,full_runtime_claim=False,independent_acceptance=False,boundary='Closed weighted prefix+one/high subtotal; Rule4 complete actual value/Nat source/split with polynomial bound OPEN; selected Rule5 answer K and forest debit split. Complete hard2/full counter/bit/native remain OPEN.'),indent=2)+'\n')
roots=sorted((R/'results').glob('algorithm-universal233-source-integration-20261016T092805Z-*'));assert B in roots
assert shutil.disk_usage(R).free>=3*(1<<30)
S=B/'source-snapshot';assert not S.exists();S.mkdir();originals=[]
for p in sorted(D.iterdir()):
 if not p.is_file() or p.name=='FINAL-MANIFEST-v1.json':continue
 s=p.stat();q=S/p.name;shutil.copyfile(p,q);assert sha(p)==sha(q);q.chmod(0o444)
 originals.append(dict(path=str(p.relative_to(R)),sha256=sha(p),mode=oct(s.st_mode&0o777),inode=s.st_ino,snapshot=str(q.relative_to(R))))
shutil.copyfile(T,S/T.name);(S/T.name).chmod(0o444)
files=[]
for root in roots:
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  s=p.stat()
  if s.st_nlink>1:assert not s.st_mode&0o222
  else:p.chmod(s.st_mode&0o555)
  files.append(dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size,mode=oct(p.stat().st_mode&0o777)))
for f in files:assert sha(R/f['path'])==f['sha256'] and not (R/f['path']).stat().st_mode&0o222
m=dict(version=1,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='FROZEN_AUTHOR_ORDINARY_CHILDREN_FOREST_DEBIT_WEIGHTED_SOURCE_INTEGRATION_REVIEW_PENDING',no_further_writes=True,
 target=str(T.relative_to(R)),target_sha256=sha(T),canonical_build=str(B.relative_to(R)),canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),source_snapshot=str(S.relative_to(R)),result=str((S/'RESULT-v1.md').relative_to(R)),interfaces=str((S/'INTERFACE-TRACE-v1.json').relative_to(R)),first_gap=str((S/'FIRST-GAP-v1.json').relative_to(R)),
 all_main_milestones='OPEN',full_ordinary_source_counter='OPEN',full_recursive_source_bit_payload='OPEN',native_or_ir='OPEN',independent_acceptance=False,improved_base=0,novelty='OPEN',initial_q='k-1',implicit_rho=False,
 attained=['Exact one/high source constructors/caller and Nat full forest debit split, including every affordable failed/duplicate ordinary callback.',
 'Concrete general RMAF.agreement K from actual checked payloads at ordinary and selected Rule5 forest-arm answer sites.',
 'Closed weighted polynomial*(233/100)^q bound for prefix+one/high source subtotal through the entire actual ordinary invocation tree; exact Nat subtotal recurrence and universal weighted composition theorem.',
 'Complete Rule4 caller actual value/Nat source sheet/callback split, including branch constructors and source materialization; polynomial bound still OPEN.',
 'Selected Rule5 forest-arm exact value/Nat forest debit split and local source plus actual forest counter.'],
 own_proof_modules=sorted({e['module'] for e in c['new_producers'] if e['full_proof_bodies']}),actual_imported_modules=c['actual_imported_modules'],reused_producer_modules=len(c['reused_producers']),fresh_producer_modules=c['fresh_producer_modules'],full_proof_body_modules=c['full_proof_body_modules'],stored_declarations=c['stored_declarations'],axiom_union=c['axiom_union'],
 version_compatibility=dict(modules=21,metadata_modules=sum(e['metadata_bridge'] is not None for e in c['version_compatibility']),decision='Exact original-context source/type/nonproof-body comparison plus full ConstantInfo datatype/constructor/recursor metadata bridge when required.',evidence=c['version_compatibility']),
 body_qualification='Full actual proof bodies for six owned proof modules. Six selected builder/execution modules and one new control module retain full nonproof bodies and actual proof-reference/axiom closure with explicit theorem-proof-text omission. Old frozen qualified records preserved.',
 controls='Six known-answer source control theorems passed; duplicate and literal-empty-region corruptions both rejected mathematically; exact original metadata bridge corruption caught; reused controlled compressed producer engine and per-compile resource/known/false controls. Same-author verification only.',
 retained_audit_failures=[str((B/'author-audit-v1/certificate.json').relative_to(R))],retained_setup_failures=json.loads((D/'SETUP-FAILURES-v1.json').read_text()),previous_pin_recheck=previous,
 first_remaining_owned_statement=json.loads((D/'FIRST-GAP-v1.json').read_text())['first_remaining_owned_statement'],remaining=json.loads((D/'FIRST-GAP-v1.json').read_text()),original_development_sources=originals,no_write_boundary='This manifest, its exact canonical copy, and immutable_files; original development file modes/inodes preserved by exact readonly snapshots.',immutable_files=files)
F=D/'FINAL-MANIFEST-v1.json';assert not F.exists();F.write_text(json.dumps(m,indent=2)+'\n');F.chmod(0o444);Q=B/F.name;shutil.copyfile(F,Q);Q.chmod(0o444)
print(m['status']);print('manifest',str(F.relative_to(R)));print('sha256',sha(F));print('immutable_files',len(files));print('interfaces',len(interfaces))
