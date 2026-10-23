"""One-shot framing-review receipt reader; no theorem/solver replay.

Consulted tools/README.md and emitall/GUIDE.md. Emitall covers declarative
headline comparisons; this bounded reader additionally resolves two differently
rooted manifests and locates verbatim source quotations. It is left local
because its paths and expected strings belong only to this frozen review.
"""
from pathlib import Path
import hashlib
import json
import time

ROOT = Path('/Users/paurel/Documents/ChatGPT/bootscience')
OWN = Path(__file__).resolve().parent
AUTHOR = ROOT / 'research/rmaf/algorithm/universal233/binary_cheap'
SEALED = ROOT / 'research/rmaf/algorithm/verification/binary-cheap-2026-10-15/sol-review-CONFIRMED-v1'
REVIEW = SEALED / 'review'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def exact_quote(text, quote):
    return quote in text

# Fixed controls precede real record comparison. A changed byte/quote must fail.
assert sha(b'abc') == 'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
assert sha(b'abd') != 'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
assert exact_quote('the local source tree', 'local source')
assert not exact_quote('the local source tree', 'whole source')
assert not exact_quote('', 'local source')
started = time.monotonic()
manifests = []
for path, expected in [
    (AUTHOR / 'BINARY-CHEAP-MANIFEST-v1.json', '3936cb4b0a5d390972ad7b1fdace4166faa9a372cc9232329294a0f2b346d839'),
    (SEALED / 'MANIFEST.json', 'c95942cce328646d13ab78f23313ff8cbb94ae576d8e6ab8ff1c243591768ee0'),
]:
    raw = path.read_bytes()
    assert sha(raw) == expected, path
    data = json.loads(raw)
    lists = {k:len(v) for k,v in data.items() if isinstance(v,list)}
    manifests.append({'path':str(path.relative_to(ROOT)), 'sha256':expected, 'list_lengths':lists})

paths = [
    AUTHOR / 'RESULT.md', AUTHOR / 'INTERFACE.md', AUTHOR / 'FIRST-GAP.md',
    REVIEW / 'FINAL-REPORT-v1.md', REVIEW / 'ERRATUM-ORIGIN-AUDIT-v1.md',
    REVIEW / 'consumer-interface-trace-v1.json',
    *[REVIEW / 'src' / name for name in ['SelectedContinuation.lean','Continuation.lean','SelectedHigh.lean','Symmetry.lean','KeptConsumers.lean','Optimality01.lean','TargetGeometry.lean']],
    *[REVIEW / name for name in ['producer-data-scientific-comparison-v1.json','producer-adoption-comparison-v4.json','producer-data-controls-comparison-v1.json','compiled-readout-comparison-v1.json','compiled-battery-comparison-v1.json','compiled-pilot-comparison-v1.json','compiled-primitive-comparison-v1.json','compiled-separation-comparison-v1.json','final-literal-malformed-pin-controls-v1.json','prior-review-producer-audit-coverage-v1.json','fingerprint-normalization-freeze-v2.json','CONTACTS-v1.json']],
]
sealed_entries = json.loads((SEALED / 'MANIFEST.json').read_text())['entries']
sealed_map = {e['path']:e for e in sealed_entries}
author_data = json.loads((AUTHOR / 'BINARY-CHEAP-MANIFEST-v1.json').read_text())
author_entries = author_data['immutable_files']
assert len(author_entries) == author_data['entry_count'] == 280
integrity = []
for path in paths:
    if not path.exists():
        integrity.append({'path':str(path.relative_to(ROOT)), 'status':'MISSING-named-path'})
        continue
    raw = path.read_bytes()
    if path.is_relative_to(SEALED):
        key = str(path.relative_to(SEALED))
    else:
        key = 'author-freeze/root/' + str(path.relative_to(ROOT))
    entry = sealed_map.get(key)
    assert entry is not None, key
    assert sha(raw) == entry['sha256'], key
    assert len(raw) == entry['bytes'], key
    integrity.append({'path':str(path.relative_to(ROOT)), 'sha256':sha(raw), 'bytes':len(raw), 'sealed_entry':key, 'status':'MATCH'})

quotations = [
('E01', AUTHOR/'RESULT.md', 'The accepted output has the exact full classes [A_yes,A_no,B,C], cost three, and valid source and target embeddings.'),
('E02', AUTHOR/'RESULT.md', 'DepthOne returns a globally minimum one-cut certificate on its original restricted source tree.'),
('E03', AUTHOR/'RESULT.md', 'inventories declarations by actual Lean module origin, checks all observed axioms'),
('E04', AUTHOR/'RESULT.md', 'No complete algorithm, novelty, global runtime, or new source-operation cost correspondence is claimed.'),
('E05', AUTHOR/'INTERFACE.md', 'original A/B disagreement, C agreement, the literal G-selected mutually-clear binary edge, C-versus-A/B clearance, and literal q3 A-clear probe acceptance.'),
('E06', AUTHOR/'INTERFACE.md', 'It permits overlap between B pieces and makes no assertion that an arbitrary opposite-core output is already an agreement forest.'),
('E07', AUTHOR/'INTERFACE.md', 'Mapping that address into the whole original S and combining it with whole-source cuts remains a later obligation.'),
('E08', AUTHOR/'FIRST-GAP.md', 'No theorem here discounts a residual query from a positive own minimum.'),
('E09', REVIEW/'FINAL-REPORT-v1.md', 'Agreement is false because whole B is rooted-bad.'),
('E10', REVIEW/'FINAL-REPORT-v1.md', 'Its two B pieces {6,8} and {5,7} overlap in target. That occurrence was retained.'),
('E11', REVIEW/'FINAL-REPORT-v1.md', 'A valid local capped answer with cuts 00 and 01 has cost 2 despite minimum 1, so the minimum supplies no unit discount for every capped query.'),
('E12', REVIEW/'FINAL-REPORT-v1.md', 'Native identical output twins contribute twice to rawQMass.'),
('E13', REVIEW/'FINAL-REPORT-v1.md', 'A no-larger Fprime is an agreement refining one output. Fprime is a correctness witness here.'),
('E14', REVIEW/'ERRATUM-ORIGIN-AUDIT-v1.md', 'The binary-cheap merged environment contains 3590 distinct names.'),
('E15', REVIEW/'ERRATUM-ORIGIN-AUDIT-v1.md', 'The 102 stored producer arrays contain 3616 declaration occurrences, including 26 extra occurrences across 23 repeated-name groups.'),
('E16', REVIEW/'ERRATUM-ORIGIN-AUDIT-v1.md', 'The merged view resolves the shared axiom name to the earlier theorem and falsely accepts ProducerToyBad as standard-axiom-clean.'),
('E17', REVIEW/'FINAL-REPORT-v1.md', 'Types and values match after the registered alpha-normalization of bound-variable names and private-to-user constant/projection names.'),
('E18', REVIEW/'FINAL-REPORT-v1.md', 'The 135 pilot comparisons are included in the 591 main comparisons.'),
('E19', REVIEW/'FINAL-REPORT-v1.md', 'Of the older 78 good-parent positive modules, 71 have identical sources in this newly audited closure; the seven absent old control modules were not newly audited.'),
('E20', REVIEW/'FINAL-REPORT-v1.md', 'The author recorded the corrected order as development contact before the universal proof.'),
('E21', REVIEW/'FINAL-REPORT-v1.md', 'Additional Expr metadata was initially collected before its dedicated toy controls; the first comparison was blocked by those controls.'),
('E22', REVIEW/'FINAL-REPORT-v1.md', 'This review uses the same checker lineage and adds zero independent replications.'),
]
quote_receipts=[]
for ident,path,quote in quotations:
    text = path.read_text()
    assert exact_quote(text,quote), (ident,path)
    line = text[:text.index(quote)].count('\n')+1
    quote_receipts.append({'id':ident,'path':str(path.relative_to(ROOT)),'line':line,'verbatim':quote,'status':'READ-VERBATIM'})

summaries={}
for name in ['producer-data-scientific-comparison-v1.json','producer-adoption-comparison-v4.json','producer-data-controls-comparison-v1.json','compiled-readout-comparison-v1.json','compiled-battery-comparison-v1.json','compiled-pilot-comparison-v1.json','compiled-primitive-comparison-v1.json','compiled-separation-comparison-v1.json','final-literal-malformed-pin-controls-v1.json','prior-review-producer-audit-coverage-v1.json','fingerprint-normalization-freeze-v2.json','CONTACTS-v1.json']:
    path=REVIEW/name
    if not path.exists():
        continue
    data=json.loads(path.read_text())
    summaries[name] = {k: v if not isinstance(v,(list,dict)) else {'type':type(v).__name__,'length':len(v)} for k,v in data.items()}
    if isinstance(data.get('checks'),list):
        summaries[name]['receipt_checks_count'] = len(data['checks'])
        summaries[name]['receipt_pass_count'] = sum(row.get('pass') is True for row in data['checks'])
        summaries[name]['failed_receipt_rows'] = [row for row in data['checks'] if row.get('pass') is not True]
    if isinstance(data.get('observation'),dict):
        summaries[name]['observation_fields'] = data['observation']
    if name == 'prior-review-producer-audit-coverage-v1.json':
        summaries[name]['coverage_categories'] = {}
        for row in data['exact_sources']:
            for key,val in row.items():
                if isinstance(val,bool):
                    summaries[name]['coverage_categories'][key] = summaries[name]['coverage_categories'].get(key,0)+int(val)
    if name == 'producer-data-scientific-comparison-v1.json':
        summaries[name]['inventory_fields'] = {k:v if not isinstance(v,(dict,list)) else {'type':type(v).__name__,'length':len(v)} for k,v in data['inventory'].items()}

out={'scope':'byte/quote/receipt checks only; no scientific replay','controls':'SHA256 known answer passes; one-byte corruption rejected; clean quote passes; changed and absent quotes rejected before comparisons','manifests':manifests,'selected_integrity':integrity,'quotations':quote_receipts,'receipt_summaries':summaries,'elapsed_seconds':time.monotonic()-started}
bank=json.loads((REVIEW/'compiled-battery-comparison-v1.json').read_text())
selected=[]
for item in bank['observations']:
    if item['id'] not in ['hand-good-A-overlapping-Bpieces','reused-two-high-actual-selector']:
        continue
    row={k:item[k] for k in ['id','source_P','partition_P','A_good','B_good','C_good','C_clear','probe','selector','selector_swap','sector_good','masses']}
    row['outputs']={side:[{k:f[k] for k in ['agreement','source_embeddings','target_embeddings','parent_refinement','output']} for f in facts] for side,facts in item['output_facts'].items()}
    row['local_A']=item['local_A']
    row['appended_raw']=item['appended_raw']
    selected.append(row)
out['selected_stored_observations']=selected
(OWN/'selected-stored-observations-v1.json').write_text(json.dumps({'source':str((REVIEW/'compiled-battery-comparison-v1.json').relative_to(ROOT)),'source_sha256':sha((REVIEW/'compiled-battery-comparison-v1.json').read_bytes()),'meaning':'retrieved stored outputs/booleans only; no re-execution or independent graph check','observations':selected},indent=2)+'\n')
(OWN/'receipt-checks-v2.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'manifest_lengths':manifests,'spotchecks':len(integrity),'matches':sum(r['status']=='MATCH' for r in integrity),'missing':[r['path'] for r in integrity if r['status']!='MATCH'],'quotes':len(quote_receipts),'selected_stored_ids':[r['id'] for r in selected],'elapsed_seconds':out['elapsed_seconds']},indent=2))
