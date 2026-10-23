from pathlib import Path
import datetime,gzip,hashlib,json,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
T=R/'research/rmaf/monitoring/main-next-20261016T105728Z/MAIN-HANDLER-TARGET-v1.json';assert sha(T)=='7a2f2210eea48dd5179088da4ceab59736556291980025b6eac9d1b41355b1af';t=json.loads(T.read_text())
B=R/json.loads((D/'BUILD-v1.json').read_text())['directory'];C=B/'author-audit-v2/certificate.json';c=json.loads(C.read_text())
assert c['status']=='PASS_AUTHOR_GOOD_PAIR_FULL_SOURCE_BOUND_AND_ORDINARY_PREPARATION_STAGE'
gate=json.loads((B/'INTERFACE-DEPENDENCY-GATE-v1.json').read_text());assert gate['status']=='PASS_AUTHOR_EXACT_GOODPAIR_PREPARE_INTERFACE_DEPENDENCY_GATE' and gate['audit_sha256']==sha(C)
assert c['full_proof_body_modules']==7 and c['version_compatibility']==[] and set(c['qualified_proof_omissions'])=={'GoodPairLocalBound'}
assert c['axiom_union']==['Classical.choice','Quot.sound','propext']
for p,h in c['inputs'].items():assert sha(R/p)==h
for e in c['sources']:assert sha(B/(e['module']+'.lean'))==e['source_sha256'] and sha(B/(e['module']+'.olean'))==e['olean_sha256']
e=t['previous_completed'];F=R/e['manifest'];assert sha(F)==e['sha256'];previous=json.loads(F.read_text())
for f in previous['immutable_files']:assert sha(R/f['path'])==f['sha256']
for f in previous['original_development_sources']:
 p=R/f['path'];s=p.stat();assert sha(p)==f['sha256'] and oct(s.st_mode&0o777)==f['mode'] and s.st_ino==f['inode']
seed=json.loads((B/'SEED.json').read_text())
for p,h in seed.get('inputs',{}).items():assert sha(R/p)==h
names={'allGoodMeter_uniform', 'properBlockMeter_value', 'callsForestDebit_weighted', 'ownedMeter_bound', 'goodPairLocalSource_value', 'goodPair_dp_payload', 'ordinaryPrepareMeter_value', 'hardPaid_caseMass_uniform', 'localTarget_labels_cap', 'additionalCostMeter_value', 'hardPaidSource_uniform_bound', 'localTarget_nodes_cap', 'appendLabelsMeter_value', 'ordinaryPrepareMeter_bound', 'localTargetMeter_value', 'goodPair_dp_bound', 'ownedMeter_value', 'goodPairSource_value', 'goodPairLocalSource_bound', 'ordinarySlotMeter_value', 'goodPairSource_bound', 'callsForestDebit_split', 'ordinarySlotMeter_bound', 'goodPairSource_split', 'selected_goodPairSource_bound', 'goodPair_checked_bound', 'properBlockMeter_bound', 'localTargetMeter_bound'}
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
(D/'INTERFACE-TRACE-v1.json').write_text(json.dumps(dict(version=1,status='AUTHOR_SCOPED_SOURCE_INTERFACES_REVIEW_PENDING',canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),interfaces=interfaces,full_runtime_claim=False,independent_acceptance=False,boundary='Complete GoodPairDP.runPair source/value/Nat callback split and selected-edge weighted source bound; uniform hard-paid caseMass cap/bound. Complete actual ordinary properBlock/slot/prepare source/value/polynomial. Remaining scheduler/reconstruction, disjoint/BothBad/whole-hard2 source work OPEN.'),indent=2)+'\n')
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
m=dict(version=1,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='FROZEN_AUTHOR_GOOD_PAIR_COMPLETE_AND_ORDINARY_PREPARATION_SOURCE_STAGE_REVIEW_PENDING',no_further_writes=True,
 target=str(T.relative_to(R)),target_sha256=sha(T),canonical_build=str(B.relative_to(R)),canonical_import='OrdinaryPrepareBound',canonical_certificate=str(C.relative_to(R)),certificate_sha256=sha(C),interface_dependency_gate=str((B/'INTERFACE-DEPENDENCY-GATE-v1.json').relative_to(R)),interface_dependency_gate_sha256=sha(B/'INTERFACE-DEPENDENCY-GATE-v1.json'),qualified_proof_omissions=c['qualified_proof_omissions'],source_snapshot=str(S.relative_to(R)),result=str((S/'RESULT-v1.md').relative_to(R)),interfaces=str((S/'INTERFACE-TRACE-v1.json').relative_to(R)),first_gap=str((S/'FIRST-GAP-v1.json').relative_to(R)),
 all_main_milestones='OPEN',complete_hard2_source_counter='OPEN',full_ordinary_source_counter='OPEN',full_recursive_source_bit_payload='OPEN',native_or_ir='OPEN',independent_acceptance=False,improved_base=0,novelty='OPEN',initial_q='k-1',implicit_rho=False,
 attained=['Complete GoodPairDP.runPair literal source/value/Nat ordinary callback split, with all three union copies, restrictions/grouping, DP, scoring/reconstruction/check.',
 'Unconditional numeric-domain goodPairLocalSource_bound and actual selected-edge goodPairSource sharp weighted bound with c^-3 forest term, no all-good/minimum/caller-fee premise.',
 'Fixed c=233/100 caseMass cap4*c^-4 and uniform hard-paid source-bound corollary.',
 'Complete literal MafScheduler.properBlock/slot/prepare source/value and (ordinarySlotPolynomial N+8)*Q.length+2 bound, including refused full-tail upper charging.'],
 own_proof_modules=sorted({e['module'] for e in c['new_producers'] if e['full_proof_bodies']}|set(c['qualified_proof_omissions'])),actual_imported_modules=c['actual_imported_modules'],reused_producer_modules=len(c['reused_producers']),fresh_producer_modules=c['fresh_producer_modules'],full_proof_body_modules=c['full_proof_body_modules'],stored_declarations=c['stored_declarations'],axiom_union=c['axiom_union'],
 import_compatibility='Every seed source and object is byte-identical to previous root-matched canonical pool. No new package import union or object substitution. Previously qualified object metadata bridges/proof-text omissions and failures remain preserved.',
 body_qualification='Full actual proof bodies for seven new proof modules. GoodPairLocalBound full theorem-text extraction hit fixed3072MiB cap; compiled source and full actual proof-reference/axiom walk retained with explicit text omission. Control theorem proof text is omitted. Inherited Hard2SelectedGenerationBound qualification and every failed record remain preserved. No independent/native acceptance.',
 controls='Ten known-answer source theorems passed; three deliberate dropped duplicate/residual/copy corruptions rejected mathematically. Same controlled exact producer engine and compiler/resource/false controls; zero independent credit.',

 retained_compile_failures=failed,previous_pin_recheck=dict(manifest=t['previous_completed'],immutable_pins=len(previous['immutable_files']),original_source_modes_inodes_preserved=True),
 first_unprovided_consuming_statement=gap['exact_remaining_statement'],remaining=gap,original_development_sources=originals,no_write_boundary='This manifest, its exact canonical copy and immutable_files; exact readonly snapshots preserve original development source modes/inodes.',immutable_files=files)
F=D/'FINAL-MANIFEST-v1.json';assert not F.exists();F.write_text(json.dumps(m,indent=2)+'\n');F.chmod(0o444);Q=B/F.name;shutil.copyfile(F,Q);Q.chmod(0o444)
print(m['status']);print('manifest',str(F.relative_to(R)));print('sha256',sha(F));print('immutable_files',len(files));print('interfaces',len(interfaces))
