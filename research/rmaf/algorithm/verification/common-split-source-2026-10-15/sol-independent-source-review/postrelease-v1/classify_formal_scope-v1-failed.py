#!/usr/bin/env python3
"""Classification report only: the unchanged raw all-stored REJECT is retained."""
import collections,importlib.util,json,pathlib,time
P=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('own_index',P/'index_receipt.py');I=importlib.util.module_from_spec(spec);spec.loader.exec_module(I)
start=time.perf_counter();compact={};partials=[];allaxioms=set();theorems=[];kinds=collections.Counter();extras=[];maxrow=0;root=None;sciparts=[];stdparts=set()
reg=json.loads((P/'ACTUAL-AUDIT-REGISTRY-final-v1.json').read_text())
with (P/'ALL151-OCCURRENCES-v1.jsonl').open('rb') as f:
 while line:=f.readline(32*1024*1024+1):
  assert len(line)<=32*1024*1024;maxrow=max(maxrow,len(line));r=json.loads(line)
  if r['record']=='module':
   if r['module'] not in reg['scientific_modules']:stdparts.update(r['olean_parts'])
  elif r['record']=='producer_part':
   extras.extend({'producer':r['producer'],'part':r['part'],'name':n,'body_scope':'no ConstantInfo body exposed; no inspection or machine-code acceptance'} for n in r['compiler_extra_names']);sciparts.append({'producer':r['producer'],'part':r['part'],'path':r['path'],'occurrences':r['occurrences']})
  elif r['record']=='occurrence':
   s=r['stored'];c=r['closure'];kinds[s['kind']]+=1;allaxioms.update(c['axioms'])
   item={'producer':r['producer'],'part':r['part'],'index':r['index'],'name':r['stored_name'],'kind':s['kind'],'unsafe':s['unsafe'],'partial':s['partial'],'type_hash':I.typehash(s),'levels':s['levels'],'stored_hash':I.h(s),'body_present':s['body_root'] is not None,'closure':c,'resolved_origin':r['resolved_origin']}
   compact[(r['producer'],r['stored_name'])]=item
   assert not s['unsafe'] and not c['unsafe'] and not c['missing'] and not(set(c['axioms'])-I.dag.ALLOWED)
   assert s['kind']!='axiom' and r['exported_view_proof'] is None
   if s['partial']:partials.append(item)
   else:assert not c['partial'],('safe root depends on partial',item)
   if s['kind']=='theorem':
    assert not s['partial'] and not c['partial'];theorems.append(item)
   if r['stored_name']=='OrdinaryCommonSplit.common_split_derived_minimum':root=item
assert root and root['producer']=='DerivedMinimum' and root['kind']=='theorem'
for x in partials:
 assert x['name'].endswith('._unsafe_rec')
 parent=x['name'].removesuffix('._unsafe_rec');par=compact.get((x['producer'],parent))
 assert par and not par['partial'] and not par['unsafe'] and par['body_present'] and not par['closure']['partial'] and par['type_hash']==x['type_hash'] and par['levels']==x['levels'],(x['name'],par)
 x['same_producer_safe_parent']=par
sources=[pathlib.Path(v['source']) for v in reg['scientific_modules'].values()]
source_mentions=[str(s) for s in sources if '_unsafe_rec' in s.read_text()]
assert not source_mentions and len(partials)==66 and len(compact)==4238
dup=json.loads((P/'DUPLICATE-STORED-NAMES-v1.json').read_text());duplicate_equal=all(len(set(v['stored_hash'] for v in d['producers']))==1 for d in dup)
assert duplicate_equal
out={'status':'FORMAL_PROOF_SCOPE_CLEAN_RAW_ALL_STORED_GATE_REJECT_RETAINED','raw_gate_status':'REJECT','raw_gate_issues':132,'stored_occurrences':4238,'distinct_names':len({x['name'] for x in compact.values()}),'kind_counts':dict(kinds),'scientific_producers':151,'scientific_parts':len(sciparts),'theorem_occurrences':len(theorems),'all_theorem_closures_no_missing_unsafe_partial_disallowed_axiom':True,'all_nonpartial_roots_have_no_partial_dependency':True,'axiom_union':sorted(allaxioms),'actual_strong_root':root,'generated_partial_runtime_occurrences':len(partials),'partial_runtime_rows':partials,'runtime_pattern_checks':'all66 actual sameproducer safe parent, exact type/universe equality, actual parent proof closure clean; no _unsafe_rec source mentions; installed compiler behavior and independent planted control retained','partial_runtime_acceptance':'NOT_GRANTED; no executable-code equivalence proof; raw gate unchanged','qualified_theorem_axiom_views':0,'direct_scientific_axioms':0,'same_name_occurrence_excess':4238-len({x['name'] for x in compact.values()}),'duplicate_names':len(dup),'all_repeated_stored_names_exact_declaration_hash_equal':duplicate_equal,'compiler_extra_names_uninspected':len(extras),'standard_parts_pinned_and_observed':len(stdparts),'maximum_record_bytes':maxrow,'seconds':time.perf_counter()-start,'limits':['schema excludes cached Expr/Level bits and physical memory sharing','trusted installed standard binary parts pinned rather than rebuilt','generated partial runtime bodies and compiler-only extra bodies not machine-code certified','manual reading scope explicitly limited in SOURCE-READ-SCOPE-v1.md','no general caller or polynomial witness extraction; all3main/global runtime/base/novelty OPEN']}
(P/'FORMAL-SCOPE-CLASSIFICATION-v1.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');(P/'COMPILER-EXTRA-NAMES-v1.json').write_text(json.dumps(extras,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','theorem_occurrences','generated_partial_runtime_occurrences','standard_parts_pinned_and_observed','duplicate_names','all_repeated_stored_names_exact_declaration_hash_equal','seconds']}))
