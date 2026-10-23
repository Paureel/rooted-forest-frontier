from pathlib import Path
import datetime,gzip,hashlib,json,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
T=R/'research/rmaf/monitoring/next-20261016T095230Z/MAIN-HARD2-TARGET-v1.json';assert sha(T)=='6872bfde16cc1fad8c9d7208a63237aa12b4bfa11e8f6833f46f94de0f75ba5d';t=json.loads(T.read_text())
B=R/json.loads((D/'BUILD-v1.json').read_text())['directory'];C=B/'author-audit-v1/certificate.json';c=json.loads(C.read_text())
assert c['status']=='PASS_AUTHOR_HARD2_GRAPH_ROUTE_AND_PAID_OUTPUT_EXECUTION_SOURCE_STAGE'
assert c['full_proof_body_modules']==8 and c['version_compatibility']==[]
assert c['axiom_union']==['Classical.choice','Quot.sound','propext']
for p,h in c['inputs'].items():assert sha(R/p)==h
for e in c['sources']:assert sha(B/(e['module']+'.lean'))==e['source_sha256'] and sha(B/(e['module']+'.olean'))==e['olean_sha256']
e=t['previous_completed'];F=R/e['manifest'];assert sha(F)==e['sha256'];previous=json.loads(F.read_text())
for f in previous['immutable_files']:assert sha(R/f['path'])==f['sha256']
for f in previous['original_development_sources']:
 p=R/f['path'];s=p.stat();assert sha(p)==f['sha256'] and oct(s.st_mode&0o777)==f['mode'] and s.st_ino==f['inode']
names={'pairChooseMeter_value','pairChooseMeter_bound','pairProperMeter_value','pairEdgeMeter_value','pairSideMeter_value',
 'hard2ParentsMeter_value','hard2SelectMeter_value','runHard2Meter_value','runHard2Meter_bound',
 'subtreeLabelsMeter_node_cap','hard2SelectMeter_bound','hard2FrontMeter_value','hard2FrontMeter_queries','hard2FrontMeter_bound',
 'hard2FrontLocalDebit_bound','hard2FrontTreeSource_bound','ordinaryOwnedSourceSubtotal_bound',
 'checkedMeter_value','chooseMeter_value','fullOutputsSource_value','fullOutputsSource_split',
 'hardPaidOutputExecutionSource_value','hardPaidOutputExecutionSource_split'}
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
(D/'INTERFACE-TRACE-v1.json').write_text(json.dumps(dict(version=1,status='AUTHOR_SCOPED_SOURCE_INTERFACES_REVIEW_PENDING',canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),interfaces=interfaces,full_runtime_claim=False,independent_acceptance=False,boundary='Complete hard2 graph/front source and bound plus weighted owned subtotal; exact full-mode paid-output EXECUTION value/Nat callback split. Actual output generation and other remaining paid/Rule5 handlers are not metered here.'),indent=2)+'\n')
assert shutil.disk_usage(R).free>=3*(1<<30)
S=B/'source-snapshot';assert not S.exists();S.mkdir();originals=[]
for p in sorted(D.iterdir()):
 if not p.is_file() or p.name=='FINAL-MANIFEST-v1.json':continue
 s=p.stat();q=S/p.name;shutil.copyfile(p,q);assert sha(p)==sha(q);q.chmod(0o444)
 originals.append(dict(path=str(p.relative_to(R)),sha256=sha(p),mode=oct(s.st_mode&0o777),inode=s.st_ino,snapshot=str(q.relative_to(R))))
shutil.copyfile(T,S/T.name);(S/T.name).chmod(0o444)
files=[]
for p in sorted(B.rglob('*')):
 if not p.is_file():continue
 s=p.stat()
 if s.st_nlink>1:assert not s.st_mode&0o222
 else:p.chmod(s.st_mode&0o555)
 files.append(dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size,mode=oct(p.stat().st_mode&0o777)))
for f in files:assert sha(R/f['path'])==f['sha256'] and not (R/f['path']).stat().st_mode&0o222
failed=[]
for p in B.glob('compile-*/receipt.json'):
 if json.loads(p.read_text()).get('status')!='PASS_AUTHOR_GUARDED_SOURCE_COMPILE':failed.append(dict(path=str(p.relative_to(R)),sha256=sha(p)))
gap=json.loads((D/'FIRST-GAP-v1.json').read_text())
m=dict(version=1,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='FROZEN_AUTHOR_HARD2_GRAPH_ROUTE_PAID_OUTPUT_EXECUTION_SOURCE_STAGE_REVIEW_PENDING',no_further_writes=True,
 target=str(T.relative_to(R)),target_sha256=sha(T),canonical_build=str(B.relative_to(R)),canonical_import='Hard2FullOutputSource',canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),source_snapshot=str(S.relative_to(R)),result=str((S/'RESULT-v1.md').relative_to(R)),interfaces=str((S/'INTERFACE-TRACE-v1.json').relative_to(R)),first_gap=str((S/'FIRST-GAP-v1.json').relative_to(R)),
 all_main_milestones='OPEN',complete_hard2_source_counter='OPEN',full_ordinary_source_counter='OPEN',full_recursive_source_bit_payload='OPEN',native_or_ir='OPEN',independent_acceptance=False,improved_base=0,novelty='OPEN',initial_q='k-1',implicit_rho=False,
 attained=['Complete original pair-geometry selector source/value and polynomial1200*(N+1)^6 bound; hard2 original graph source/value and2100*(N+1)^6 bound.',
 'Exact hard2 graph/pendant/disjoint front route value/actual queries and partitionBudget N+2700*(N+1)^6 source bound.',
 'Closed weighted accumulated prefix+one/high+hard2-front source subtotal through full ordinary recursion.',
 'Literal full-mode paid-output execution value/Nat callback split and actual runHardPaid output-list instantiation; output GENERATION explicitly remains separate.'],
 own_proof_modules=sorted({e['module'] for e in c['new_producers'] if e['full_proof_bodies']}),actual_imported_modules=c['actual_imported_modules'],reused_producer_modules=len(c['reused_producers']),fresh_producer_modules=c['fresh_producer_modules'],full_proof_body_modules=c['full_proof_body_modules'],stored_declarations=c['stored_declarations'],axiom_union=c['axiom_union'],
 import_compatibility='Every inherited source and object is byte-identical to the previous root-matched canonical pool; no new object substitution or cross-package path union. Previously qualified metadata/version bridges remain preserved.',
 body_qualification='Full actual proof bodies for eight new proof modules; new control module retains full nonproof bodies and actual proof-reference/axiom closure with explicit theorem-proof-text omission. Old frozen qualified records preserved.',
 controls='Seven known-answer source control theorems passed; three deliberate edge/overlap/duplicate corruptions rejected mathematically. Same controlled exact compressed producer engine and per-compile guard/resource/false controls, without independent credit.',
 retained_compile_failures=failed,previous_pin_recheck=dict(manifest=t['previous_completed'],immutable_pins=len(previous['immutable_files']),original_source_modes_inodes_preserved=True),
 first_unprovided_consuming_statement=gap['first_unprovided_consuming_statement'],remaining=gap,original_development_sources=originals,no_write_boundary='This manifest, its exact canonical copy and immutable_files; exact readonly snapshots preserve original development source modes/inodes.',immutable_files=files)
F=D/'FINAL-MANIFEST-v1.json';assert not F.exists();F.write_text(json.dumps(m,indent=2)+'\n');F.chmod(0o444);Q=B/F.name;shutil.copyfile(F,Q);Q.chmod(0o444)
print(m['status']);print('manifest',str(F.relative_to(R)));print('sha256',sha(F));print('immutable_files',len(files));print('interfaces',len(interfaces))
