#!/usr/bin/env python3
# One-shot reader metadata/quotation check. Intentionally unregistered: it checks
# these pinned documents only and neither imports nor executes scientific code.
import hashlib
import json
import re
import difflib
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

ROOT = Path('/Users/paurel/Documents/ChatGPT/bootscience')
OWN = Path(__file__).resolve().parent
SEALED = ROOT/'research/rmaf/algorithm/verification/forest-solver-2026-10-15/sol-pre-candidate/post-release-v1'
AUTHOR = ROOT/'research/rmaf/algorithm/universal233/forest_solver'
FINAL_PIN = '4fc1e7c7a4dfa09c2223caa3eaa0767cd8695676f4a38b2e4dccfdf20548cec8'
AUTHOR_PIN = '89937a6f71bceb2dbeb64917b4b805e8f193fa485b00ec28acecdc95d047dcf5'

def digest(b):
    return hashlib.sha256(b).hexdigest()

def paths_valid(entries):
    names = [e['path'] for e in entries]
    return len(names) == len(set(names)) and all(
        not PurePosixPath(n).is_absolute() and '..' not in PurePosixPath(n).parts
        for n in names)

def quoted_at(text, lo, hi, quote):
    return quote in '\n'.join(text.splitlines()[lo-1:hi])

# Written expectations use constructed bytes/strings, not scientific records.
controls = {
    'empty_known_sha': digest(b'') == 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
    'wrong_hash_rejected': digest(b'') != '0'*64,
    'clean_quote': quoted_at('alpha\nbeta\n', 2, 2, 'beta'),
    'altered_quote_rejected': not quoted_at('alpha\nbeta\n', 2, 2, 'betA'),
    'mislocated_quote_rejected': not quoted_at('alpha\nbeta\n', 1, 1, 'beta'),
    'clean_members': paths_valid([{'path':'a'}, {'path':'b'}]),
    'duplicate_rejected': not paths_valid([{'path':'a'}, {'path':'a'}]),
    'escaping_path_rejected': not paths_valid([{'path':'../a'}]),
    'wrong_count_rejected': len([0, 1]) != 3,
}
assert all(controls.values()), controls

mf = SEALED/'FINAL-MANIFEST-v1.json'
am = AUTHOR/'FOREST-SOLVER-MANIFEST-v3.json'
assert digest(mf.read_bytes()) == FINAL_PIN
assert digest(am.read_bytes()) == AUTHOR_PIN
m, a = json.loads(mf.read_text()), json.loads(am.read_text())
assert len(m['entries']) == 1335 and paths_valid(m['entries'])
assert len(a['immutable_files']) == 540 and paths_valid(a['immutable_files'])
fm = {e['path']:e for e in m['entries']}
amap = {e['path']:e for e in a['immutable_files']}

sealed_reads = {
 'REVIEW-REPORT-v4.md':'full', 'SEMANTIC-REDERIVATION-v2.md':'full',
 'PREMISE-TRACE-v2.md':'full; two bounded ranges', 'ORIGIN-RULING-v3.md':'full',
 'WORK-RULING-v2.md':'full', 'CONTACT-LEDGER-v4.json':'full',
 'REVIEW-RESULT-v4.json':'full', 'ACTUAL-MASS-REALIZATION-v1.json':'full',
 'paid-scheduler-controls-full-v1.json':'full', 'DIAGNOSTIC-FAILURES-v1.json':'full',
 'SIGNATURES-AND-CLOSURES-v1.json':'two retained signatures, outer binders and constants; no closure body review',
 'WORKFILE-v1.md':'selected log lines from rg pattern raw/GB/timeout/fail/format/candidate_contact/ps/check; chronology only',
 'isolated-build-v1/ForestProgram.lean':'lines 54-100, soundness signature and ordinary/exact contracts with adjacent proof text; no replay',
 'isolated-build-v1/ForestDefs.lean':'lines 1-50, actual selector/replacement/dispatch interface',
 'isolated-build-v1/GroupState.lean':'lines 1-64, literal datatype checker definitions',
 'isolated-build-v1/ForestDisjoint.lean':'lines 100-109, final theorem signature/composition only',
}
inputs = []
def record(p, mode, pin=None, size=None):
    b=p.read_bytes()
    h=digest(b)
    if pin is not None: assert h==pin, str(p)
    if size is not None: assert len(b)==size, str(p)
    inputs.append({'path':str(p.relative_to(ROOT)), 'sha256':h, 'bytes':len(b), 'read_mode':mode})
for n,mode in sealed_reads.items():
    e=fm[n]; record(SEALED/n,mode,e['sha256'],e['size'])
for n in ['RESULT.md','INTERFACE.md','SOURCE-WORK.md','FIRST-GAP.md']:
    p=AUTHOR/n; e=amap[str(p.relative_to(ROOT))]; record(p,'full',e['sha256'])
record(mf,'parsed metadata/paths/count; not all member contents',FINAL_PIN)
record(am,'parsed metadata/paths/count; not all member contents',AUTHOR_PIN)
record(ROOT/'research/rmaf/algorithm/verification/forest-solver-referee-2026-10-15/TARGET-v1.md','full; first contact')
record(ROOT/'research/rmaf/algorithm/FOREST-SOLVER-REVIEW-STATUS-v1.md','full; separate root bytes')
for n in ['referee-sim','prose-lint','reading-contract','independence-bookkeeping','tool-stewardship','planted-truth','acceptance-gate']:
    record(ROOT/f'.agents/skills/{n}/SKILL.md','full')
record(ROOT/'bootloops/tools/README.md','full')
record(ROOT/'bootloops/tools/emitall/GUIDE.md','full')

qdata = [
 ('Q01', 'REVIEW-REPORT-v4.md',3,3,'conditional only on its printed OrdinaryIH for exact ordinary-tree calls.'),
 ('Q02', 'REVIEW-REPORT-v4.md',15,15,'The ordinary dispatcher, mutual termination, full runtime, smaller global base, novelty and later fresh-context prose/referee framing remain OPEN.'),
 ('Q03', 'SEMANTIC-REDERIVATION-v2.md',17,17,'including degree-two suppressed vertices'),
 ('Q04', 'SEMANTIC-REDERIVATION-v2.md',11,11,'No current-parent target-disjointness is used in this replacement argument.'),
 ('Q05', 'SEMANTIC-REDERIVATION-v2.md',35,35,'The one-source same-label call remains an external mutual-IH interface.'),
 ('Q06', 'ORIGIN-RULING-v3.md',11,11,'These are explicit proof-body differences, not raw exact matches; both actual and resolved bodies remain in the records.'),
 ('Q07', 'ORIGIN-RULING-v3.md',17,17,'The raw comparisons remain unequal'),
 ('Q08', 'ORIGIN-RULING-v3.md',23,23,'These are qualified Name correspondences, not raw equality across different module names.'),
 ('Q09', 'WORK-RULING-v2.md',18,18,'it does not identify every primitive operation of the production functions with that sheet.'),
 ('Q10', 'WORK-RULING-v2.md',14,14,'every proper current source list for the fixed original target, and every budget up to Q.'),
 ('Q11', 'REVIEW-REPORT-v4.md',9,9,'The 60 ordinary table pairs are test fixtures.'),
 ('Q12', 'REVIEW-REPORT-v4.md',11,11,'its failed d=1 child remains counted.'),
 ('Q13', 'CONTACT-LEDGER-v4.json',37,37,'Old receipts are unchanged and receive no blind-control credit.'),
 ('Q14', 'CONTACT-LEDGER-v4.json',39,39,'raw-repr batch timeout and uncredited output'),
 ('Q15', 'CONTACT-LEDGER-v4.json',40,40,'Platform denied ps process inspection.'),
 ('Q16', 'REVIEW-REPORT-v4.md',15,15,'without statistical independence or an extra replication count.'),
 ('Q17', 'SEMANTIC-REDERIVATION-v2.md',33,33,'No successful query discounts its own unknown minimum.'),
 ('Q18', 'SEMANTIC-REDERIVATION-v2.md',23,23,'Soundness is unconditional in the ordinary callback'),
 ('Q19', 'PREMISE-TRACE-v2.md',21,23,'∀ G, agreement t s G = true → F.length ≤ G.length'),
 ('Q20', 'PREMISE-TRACE-v2.md',973,978,'(ho : OrdinaryIH ordinary) : ExactAt (solve ordinary)'),
 ('Q21', 'WORKFILE-v1.md',89,89,'It remains uncredited timeout output'),
 ('Q22', 'WORKFILE-v1.md',59,59,'The early projection is void.'),
]
quotes=[]
for qid, filename, lo, hi, quote in qdata:
    p=SEALED/filename
    assert quoted_at(p.read_text(),lo,hi,quote),(qid,filename,lo,hi)
    quotes.append({'id':qid,'path':str(p.relative_to(ROOT)),'line_start':lo,'line_end':hi,'quote':quote})
for qid,fn,lo,hi,quote in [
 ('A01','INTERFACE.md',6,6,'only callback premise is the printed `OrdinaryIH`'),
 ('A02','SOURCE-WORK.md',3,3,'counts natural source-operation bills embedded in exact rationals.'),
 ('A03','SOURCE-WORK.md',9,9,'declared conservative local contract, still requires primitive source review'),
 ('A04','RESULT.md',11,11,'no novelty claim or full ordinary-tree algorithm claim is made.'),
 ('A05','FIRST-GAP.md',3,3,'every proper ordinary pair returns an affordable global minimum, and every affordable ordinary agreement guarantees a return.'),
 ('A06','INTERFACE.md',15,15,'The callbacks receive labelled forests, not recovered final source-cut lists.'),
]:
    p=AUTHOR/fn; assert quoted_at(p.read_text(),lo,hi,quote),qid
    quotes.append({'id':qid,'path':str(p.relative_to(ROOT)),'line_start':lo,'line_end':hi,'quote':quote})

sigs=json.loads((SEALED/'SIGNATURES-AND-CLOSURES-v1.json').read_text())['signatures']
signatures=[]
for name,expected in [
 ('GenericForest.exact_of_ordinary',['`ordinary','`ho']),
 ('GenericForest.source_work_bound',['`ordinary','`ordinaryWork','`T','`Q','`c','`K','`hc','`hK','`hlocal','`ss','`q','`hqQ','`hp'])
]:
    s=sigs[name]; dag=s['exact_type']; nodes=dag['nodes']; idx=dag['root']; outer=[]
    while nodes[idx][0]=='forallE':
        node=nodes[idx];outer.append({'name':node[1],'binder_info':node[4],'domain_root':node[2]});idx=node[3]
    assert outer==s['binders'] and [b['name'] for b in outer]==expected
    assert idx==s['result_root'] and s['universe_parameters']==[]
    assert s['kind']=='theorem' and not s['unsafe'] and not s['partial']
    assert all(b['binder_info']=='Lean.BinderInfo.default' for b in outer)
    consts=sorted({n[1] for n in nodes if n[0]=='const'})
    assert ('`GenericForest.DisjointExact' not in consts)
    if name.endswith('source_work_bound'): assert '`GenericForest.OrdinaryIH' not in consts
    signatures.append({'name':name,'outer_binders':outer,'universe_parameters':[],'result_root':idx,'constants':consts,'interpretation':'retained record checked; no Lean/kernel replay'})
r=json.loads((SEALED/'REVIEW-RESULT-v4.json').read_text())
expected_counts={'fresh_positive_scientific_modules':143,'copied_scientific_oleans':0,'stored_kernel_occurrences':4977,'unique_kernel_names':4938,'resolved_scientific_names':4938,'private_kernel_occurrences':571,'actual_resolved_proof_body_differences':7,'IR_only_auxiliary_occurrences_no_kernel_type_body':1375,'byte_identical_original_adapted_sources':129,'import_only_counterparts':14,'raw_exact_import_counterparts':11,'qualified_hygienic_import_counterparts':3,'import_counterpart_declarations_with_Name_differences':23,'original_basename_contexts':15,'source_contract_consumer_groups':64,'finite_cases':19,'finite_ordinary_fixture_pairs':60,'nodes':107,'root_rows':52,'lifted_forests':241,'raw_occurrences':55,'covered_forests':92,'actual_paid_scheduler_scalar_cases':4}
assert all(r['executed'][k]==v for k,v in expected_counts.items())
assert r['mass_counterextension']['raw_costs']==[1,2,2]
assert r['mass_counterextension']['mass']=='14/9' and r['mass_counterextension']['bound']=='4/3'
assert r['mass_counterextension']['failed_d1_child_still_counted'] is True
assert r['paid_scheduler_fixture_realization']['two_minima_2_q3_calls']==[]
assert r['paid_scheduler_fixture_realization']['two_minima_2_q4_calls']==[2,2]
assert r['paid_scheduler_fixture_realization']['second_failure_recursive_bill']==25
assert r['paid_scheduler_fixture_realization']['undercharged_failure_false_bill']==12
assert r['paid_scheduler_fixture_realization']['own_minimum_discount_false_trace']==[2,0]
assert r['VERIFIED_CLOSED'] is False

out={'schema':'scoped-reader-bounded-records-v1','utc':datetime.now(timezone.utc).isoformat(),'controls':controls,'controls_context':'post-contact metadata controls only; no blind or scientific replication credit','pins':{'final':FINAL_PIN,'author':AUTHOR_PIN},'manifest_path_counts':{'final':1335,'author':540},'selected_inputs':inputs,'quote_receipts':quotes,'retained_signatures':signatures,'reported_count_fields_checked':expected_counts,'checks_passed':True,'scope':'selected input bytes and recorded fields only; root 1335-member integrity outcome is retrieved, not repeated; no theorem/kernel/solver replay','contact_history':[{'order':1,'event':'root task and target supplied exact pins; TARGET read first; skeleton saved immediately'},{'order':2,'event':'required skills and named frozen review/author records read; no live successor or checker implementation'},{'order':3,'event':'bounded metadata controls then selected input hash/quote/retained-type checks; all post-contact'},{'order':4,'event':'two self-lint passes; draft/pass-one snapshots and exact diff retained'},{'order':5,'event':'root coordination only; no author/peer messages, children, uploads or hosting'}],'diagnostic_limits':'WORK-LOG-v1.md retains partial-output, path-discovery and signature-preview limitations; no scientific receipt was changed','root_different_editor':'PENDING','render':'Markdown source read only; no actual app/PDF render inspected'}
(OWN/'CONTACT-AND-EVIDENCE-LEDGER-v1.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks_passed':True,'controls':len(controls),'selected_inputs':len(inputs),'quotes':len(quotes),'retained_signatures':len(signatures),'manifest_paths':[len(m['entries']),len(a['immutable_files'])]}))

# Final Markdown source checks; no rendered-output or semantic proof claim.
texts={n:(OWN/n).read_text() for n in ['REVIEW-REPORT-v1.md','SCOPE-COMPANION-v1.md']}
prose_quotes=[]
for n,txt in texts.items():
    for lineno,line in enumerate(txt.splitlines(),1):
        assert line.count('`')%2==0,(n,lineno,'inline-code delimiter')
        for quote in re.findall('“([^”]+)”',line):
            matches=[]
            for inp in inputs:
                p=ROOT/inp['path']
                content=p.read_text()
                if quote in content:
                    pos=content.index(quote)
                    matches.append({'path':inp['path'],'line':content[:pos].count('\n')+1})
            assert matches,(n,lineno,quote)
            prose_quotes.append({'file':n,'line':lineno,'quote':quote,'matches':matches})
    assert txt.count('“')==txt.count('”'),n
    assert '<!--' not in txt and '-->' not in txt,n
    assert all(term in txt for term in ['OrdinaryIH','LocalBillBound','c>=2','q<=Q','K>=0']),n
    assert 'novelty acceptance remain open' in txt or 'novelty acceptance remain OPEN' in txt,n
    assert 'same model family' in txt or n=='REVIEW-REPORT-v1.md',n

def tables(txt):
    blocks=[]; current=[]
    for line in txt.splitlines()+['']:
        if line.startswith('|'): current.append(line)
        elif current: blocks.append(current); current=[]
    return blocks
blocks=tables(texts['REVIEW-REPORT-v1.md'])
assert len(blocks)==2
assert all(len(line.split('|'))==6 for line in blocks[0])
assert all(len(line.split('|'))==5 for line in blocks[1])
assert len(blocks[0])-2==10 and len(blocks[1])-2==7
for audience in ['Parameterized-MAF expert','Rooted-phylogenetic practitioner','Lean expert','Implementation/API user','Beginner']:
    rows=[l for l in blocks[0][2:] if l.startswith('| '+audience+' |')]
    assert len(rows)==2 and sum('Correctness:' in x for x in rows)==1 and sum('Novelty:' in x for x in rows)==1,audience

diffs=[]
for filename in texts:
    base=filename.replace('-v1.md','-prelint-v1.md')
    passone=filename.replace('-v1.md','-pass1-v1.md')
    for before,after,label in [(base,passone,'pass-one'),(passone,filename,'pass-two/final')]:
        diffs.append('# '+label+' '+filename+'\n')
        diffs.extend(difflib.unified_diff((OWN/before).read_text().splitlines(True),(OWN/after).read_text().splitlines(True),fromfile=before,tofile=after))
(OWN/'REVIEW-DIFF-v1.diff').write_text(''.join(diffs))
prose={'schema':'source-prose-check-v1','source_only':True,'actual_render_inspected':False,'root_different_editor':'PENDING','audience_rows':10,'audiences':5,'surface_rows':7,'all_smart_quote_spans_have_input_receipts':True,'smart_quote_spans':prose_quotes,'inline_code_delimiters_paired_per_line':True,'tables_have_expected_columns':True,'required_scope_tokens_present':True,'semantic_number_honesty_and_two_self_passes':'LINT-AND-DIFF-LOG-v1.md','passed':True}
(OWN/'PROSE-CHECK-v1.json').write_text(json.dumps(prose,indent=2)+'\n')
print(json.dumps({'source_prose_checks_passed':True,'quote_spans':len(prose_quotes),'audience_rows':10,'surface_rows':7,'actual_render':False,'root_editor':'PENDING'}))
