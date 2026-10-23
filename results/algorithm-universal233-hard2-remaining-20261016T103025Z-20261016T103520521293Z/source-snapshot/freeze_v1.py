from pathlib import Path
import datetime,gzip,hashlib,json,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
T=R/'research/rmaf/monitoring/next-20261016T103025Z/MAIN-HARD2-REMAINING-TARGET-v1.json';assert sha(T)=='1d7630704bd30255e2c3b8f09fdac57e1790d43760ae211230d5a4f874866e29';t=json.loads(T.read_text())
B=R/json.loads((D/'BUILD-v1.json').read_text())['directory'];C=B/'author-audit-v2/certificate.json';c=json.loads(C.read_text())
assert c['status']=='PASS_AUTHOR_COMPLETE_HARD_PAID_SOURCE_UNIT_BOUND_REMAINING_HANDLERS_OPEN'
gate=json.loads((B/'INTERFACE-DEPENDENCY-GATE-v2.json').read_text());assert gate['status']=='PASS_AUTHOR_EXACT_HARD_PAID_INTERFACE_DEPENDENCY_GATE' and gate['audit_sha256']==sha(C)
assert c['full_proof_body_modules']==6 and len(c['version_compatibility'])==29 and set(c['qualified_proof_omissions'])=={'Hard2SelectedGenerationBound'}
assert c['axiom_union']==['Classical.choice','Quot.sound','propext']
for p,h in c['inputs'].items():assert sha(R/p)==h
for e in c['sources']:assert sha(B/(e['module']+'.lean'))==e['source_sha256'] and sha(B/(e['module']+'.olean'))==e['olean_sha256']
e=t['previous_completed'];F=R/e['manifest'];assert sha(F)==e['sha256'];previous=json.loads(F.read_text())
for f in previous['immutable_files']:assert sha(R/f['path'])==f['sha256']
for f in previous['original_development_sources']:
 p=R/f['path'];s=p.stat();assert sha(p)==f['sha256'] and oct(s.st_mode&0o777)==f['mode'] and s.st_ino==f['inode']
seed=json.loads((B/'SEED.json').read_text())
for p,h in seed['inputs'].items():assert sha(R/p)==h
for key in ['actual_recovery_source','optimizer_fees']:
 entry=t['allowed_packages'][key];mp=R/entry['manifest'];assert sha(mp)==entry['sha256'];mm=json.loads(mp.read_text())
 for e in mm.get('original_files',[]):
  if not isinstance(e,dict):continue
  p=R/e['path'];st=p.stat();assert sha(p)==e['sha256']
  if 'mode' in e:assert oct(st.st_mode&0o777)==e['mode']
  if 'inode' in e:assert st.st_ino==e['inode']
  if 'device' in e:assert st.st_dev==e['device']
names={'hardPaidSource_value', 'caseOutputsMeter_value', 'actualOutputsMeter_value', 'kindOutputsMeter_value', 'binary_prefix_absorb', 'hardPaidSource_bound', 'generationEnvelope_uniform', 'actual_output_count', 'actual_output_shape', 'actual_output_generated', 'wholeOutputsMeter_value', 'outputForestDebit_weighted', 'hardPaidSource_split', 'outputKindCap_uniform', 'caseOutputsMeter_bound', 'generatedOutputsMeter_bound', 'actualOutputsMeter_bound', 'fullOutputsSource_local', 'wholeOutputsMeter_bound', 'kindOutputsMeter_bound', 'generate_output_count', 'generatedOutputsMeter_value', 'selected_result_size'}
interfaces=[]
for e in c['new_producers']:
 p=R/e['path'];assert sha(p)==e['sha256']
 with gzip.open(p,'rt') as f:rows=json.load(f)
 for r in rows:
  short=r['actual_name'].split('.')[-1]
  if short in names:
   assert r['kind']=='theorem'
   if e['full_proof_bodies']:assert r['has_body'] and r['body_text_scope']=='FULL_ALL_BODY' and r['body']!='<none>'
   else:assert e['module'] in c['qualified_proof_omissions'] and r['body_text_scope']=='OMITTED_THEOREM_PROOF_TEXT'
   src=B/(e['module']+'.lean');s=src.read_text();match=re.search(r'^.*theorem '+re.escape(short)+r'\b',s,re.M);assert match
   interfaces.append(dict(name=r['actual_name'],module=e['module'],source=str(src.relative_to(R)),line=s[:match.start()].count('\n')+1,type_sha256=hashlib.sha256(r['type'].encode()).hexdigest(),body_sha256=hashlib.sha256(r['body'].encode()).hexdigest() if e['full_proof_bodies'] else None,body_bytes=len(r['body']) if e['full_proof_bodies'] else None,proof_text_scope=r['body_text_scope'],actual_full_reference_sha256=hashlib.sha256(json.dumps(r['direct_references']).encode()).hexdigest(),axioms=r['axiom_references'],record=e['path'],record_sha256=e['sha256']))
assert {e['name'].split('.')[-1] for e in interfaces}==names
(D/'INTERFACE-TRACE-v1.json').write_text(json.dumps(dict(version=1,status='AUTHOR_SCOPED_SOURCE_INTERFACES_REVIEW_PENDING',canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),interfaces=interfaces,full_runtime_claim=False,independent_acceptance=False,boundary='Complete actual Hard2PaidLocal.actualOutputs/runHardPaid source value, Nat callback split and closed sharp-mass weighted source-unit bound. Good-pair, disjoint scheduling, both-bad and complete hard2/ordinary counters remain OPEN.'),indent=2)+'\n')
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
m=dict(version=1,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='FROZEN_AUTHOR_COMPLETE_HARD_PAID_SOURCE_UNIT_BOUND_OTHER_HANDLERS_OPEN_REVIEW_PENDING',no_further_writes=True,
 target=str(T.relative_to(R)),target_sha256=sha(T),canonical_build=str(B.relative_to(R)),canonical_import='HardPaidSourceBound',canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),interface_dependency_gate=str((B/'INTERFACE-DEPENDENCY-GATE-v2.json').relative_to(R)),interface_dependency_gate_sha256=sha(B/'INTERFACE-DEPENDENCY-GATE-v2.json'),qualified_proof_omissions=c['qualified_proof_omissions'],source_snapshot=str(S.relative_to(R)),result=str((S/'RESULT-v1.md').relative_to(R)),interfaces=str((S/'INTERFACE-TRACE-v1.json').relative_to(R)),first_gap=str((S/'FIRST-GAP-v1.json').relative_to(R)),
 all_main_milestones='OPEN',complete_hard2_source_counter='OPEN',full_ordinary_source_counter='OPEN',full_recursive_source_bit_payload='OPEN',native_or_ir='OPEN',independent_acceptance=False,improved_base=0,novelty='OPEN',initial_q='k-1',implicit_rho=False,
 attained=['Reused exact completed RWInitial.meterGenerate source meter, including initialization/color/output fees; no initializer reproof.',
 'Complete literal clique/four/diagonal/vertex/side/edge/case/actual output generation meters with universal value equality and selected original geometric address bounds.',
 'Complete literal runHardPaid source value/Nat ordinary callback split, including generation, original agreement checks, minimum selection and all output occurrences.',
 'Closed hardPaidSource_bound: (hardPaidPolynomial N Q + geometric c*forestCoefficient N Q*caseMass c out)*c^q, c=233/100, proper selected original source domain, treeNodes capsN>=3,q<=Q. Every forest debit uses its own actual residual q-d.'],
 own_proof_modules=sorted({e['module'] for e in c['new_producers'] if e['full_proof_bodies']}|set(c['qualified_proof_omissions'])),actual_imported_modules=c['actual_imported_modules'],reused_producer_modules=len(c['reused_producers']),fresh_producer_modules=c['fresh_producer_modules'],full_proof_body_modules=c['full_proof_body_modules'],stored_declarations=c['stored_declarations'],axiom_union=c['axiom_union'],
 import_compatibility='Chosen seed preserves the previous pool. Exact original recovery five-directory context and480-module closure pinned;29 same-source/different-object imports compare exact type/nonproof bodies and complete ConstantInfo metadata for other declaration kinds. Header confirms every loaded object. Original qualified records preserved.',
 body_qualification='Full actual proof bodies for six new proof modules. Hard2SelectedGenerationBound full proof-text extraction exceeded fixed3072MiB cap; its source compiles and producer retains full actual proof-reference/axiom closure with explicitly omitted proof text. Other fresh dependency/control producers also qualify proof-text omission. Every failed/old qualified record is preserved. No independent or native acceptance.',
 controls='Eight known-answer source theorems passed; three deliberate dropped invocation/color fee/left-copy corruptions rejected mathematically. Full ConstantInfo corruption rejected. Same controlled exact compressed producer engine and per-compile guard/resource/false controls, without independent credit.',
 retained_compile_failures=failed,previous_pin_recheck=dict(manifest=t['previous_completed'],immutable_pins=len(previous['immutable_files']),original_source_modes_inodes_preserved=True),
 first_unprovided_consuming_statement=gap['exact_remaining_statement'],remaining=gap,original_development_sources=originals,no_write_boundary='This manifest, its exact canonical copy and immutable_files; exact readonly snapshots preserve original development source modes/inodes.',immutable_files=files)
F=D/'FINAL-MANIFEST-v1.json';assert not F.exists();F.write_text(json.dumps(m,indent=2)+'\n');F.chmod(0o444);Q=B/F.name;shutil.copyfile(F,Q);Q.chmod(0o444)
print(m['status']);print('manifest',str(F.relative_to(R)));print('sha256',sha(F));print('immutable_files',len(files));print('interfaces',len(interfaces))
