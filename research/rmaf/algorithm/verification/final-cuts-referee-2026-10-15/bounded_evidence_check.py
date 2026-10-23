#!/usr/bin/env python3
"""One-shot metadata/quote check for this sealed framing review, not a solver audit.

emitall was consulted; this script adds selected-file authentication across two
manifest schemas. It deliberately does not load or compare all scientific modules.
"""
import hashlib
import json
from pathlib import Path
import time

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[4]
A = Path('research/rmaf/algorithm/universal233/final_cut_recovery')
R = Path('research/rmaf/algorithm/verification/final-cuts-2026-10-15')
def digest(b):
    return hashlib.sha256(b).hexdigest()
def need(got, expected):
    if got != expected:
        raise AssertionError((got, expected))
def rejects(f):
    try:
        f()
    except AssertionError:
        return True
    raise AssertionError('corruption did not reject')

start = time.perf_counter()
need(digest(b''), 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855')
need(digest(b'abc'), 'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad')
rejects(lambda: need(digest(b'abd'), digest(b'abc')))
toy = [json.loads(x) for x in ['{"id":1}', '{"id":2}']]
need(len(toy), 2)
rejects(lambda: need(len(toy), 1))
controls = {'known_hashes': 2, 'corrupt_hash_rejected': True,
            'two_record_parser': True, 'wrong_count_rejected': True}

manifest_a = A / 'FINAL-CUTS-MANIFEST-v1.json'
manifest_r = R / 'ARTIFACTS.json'
need(digest((ROOT / manifest_a).read_bytes()), '95569c46912bff25f74cd01174bc51a934e7395524922271e6de4538fbdc4fb3')
need(digest((ROOT / manifest_r).read_bytes()), '4699c40246839ad60e860f3ae280e6b159cb7e3a00e0383d0b5359b9780bbc71')
ma = json.loads((ROOT / manifest_a).read_text())
mr = json.loads((ROOT / manifest_r).read_text())
amap = {x['path']: x['sha256'] for x in ma['immutable_files']}
rmap = mr['file_hashes']
need(len(amap), 618)
need(len(rmap), 254)
need(mr['file_count'], len(rmap))

selected = [A/x for x in ['RESULT.md','INTERFACE.md','FIRST-GAP.md']]
selected += [R/x for x in ['RESULT.md','CONSUMER-TRACE.md','SOURCE-COST-REVIEW.md',
 'INSTRUMENT-HISTORY.md','ACTUAL-COMPARISON.json','ACTUAL.stdout.log',
 'POST-CANDIDATE-SCOPE-RECEIPT.json','REPLAY.json','CONTROL-PIN.json',
 'candidate-logs/IndependentAudit.log','candidate-logs/ReviewUse.log',
 'frozen-inputs/CORE-COST-CORRESPONDENCE.md',
 'isolated/RecoveryProgram.lean','isolated/Recovery.lean','isolated/Realization.lean',
 'isolated/OriginalGraph.lean','isolated/CoreProgram.lean','isolated/Permutations.lean',
 'isolated/FinalWork.lean','isolated/ReviewUse.lean']]
hashes = {}
for rel in selected:
    expected = amap[str(rel)] if str(rel) in amap else rmap[str(rel)]
    got = digest((ROOT/rel).read_bytes())
    need(got, expected)
    hashes[str(rel)] = got

actual = json.loads((ROOT/R/'ACTUAL-COMPARISON.json').read_text())
raw = [json.loads(x.removeprefix('ACTUAL_VALUE ')) for x in
       (ROOT/R/'ACTUAL.stdout.log').read_text().splitlines() if x.startswith('ACTUAL_VALUE ')]
recover = [x for x in raw if 'recover' in x]
cert = [x for x in raw if 'cutEdges' in x]
alts = [x for x in cert if '-allowed-history-' in x['id']]
need((len(recover),sum(x['recover'] is not None for x in recover),
      sum(x['recover'] is None for x in recover),len(cert),len(alts)), (22,12,10,16,9))
need((actual['actual_recovery_cases'],actual['valid_recovery_cases'],actual['refused_cases'],
      actual['original_address_cases'],actual['reference_permutation_cases']), (22,12,10,16,2))
pin = json.loads((ROOT/R/'CONTROL-PIN.json').read_text())
need(sum(x['op']=='permutation' for x in pin['controls']), 2)
cross = next(x for x in recover if x['id']=='source-valid-target-crossed')
need((cross['inputCheck'],cross['targetAgreement'],cross['returnedTargetAgreement']), (True,False,False))
need(len(cross['rawOutputs']), 1)
huge = next(x for x in recover if x['id']=='huge-original-labels')
need({x['label'].bit_length() for x in huge['colors']}, {129})
need({x['color'].bit_length() for x in huge['colors']}, {129})
repeat = next(x for x in raw if x['id']=='repeated-per-branch-not-free')
need((repeat['charged'],repeat['factor'],repeat['absorbed']), (64,8,False))

replay = json.loads((ROOT/R/'REPLAY.json').read_text())
records = [json.loads(x.removeprefix('REVIEW_ORIGIN ')) for x in
           (ROOT/R/'candidate-logs/IndependentAudit.log').read_text().splitlines()
           if x.startswith('REVIEW_ORIGIN ')]
named = ['Universal233.FinalCutRecovery.'+x for x in
         ['recover_checked','recover_sound','recover_success_iff','recover_original_agreement',
          'final_work_bound','final_work_absorbed']]
picked = {}
for name in named:
    matches = [x for x in records if x['name']==name]
    need(len(matches), 1)
    entry = matches[0]
    need(entry['kind'], 'theorem')
    if not set(entry['axioms']) <= {'Classical.choice','Quot.sound','propext'}:
        raise AssertionError(entry['axioms'])
    picked[name] = entry

quotes = {
 'source_guards': (R/'isolated/RecoveryProgram.lean',14),
 'literal_generate_head': (R/'isolated/RecoveryProgram.lean',17),
 'agreement_premise': (R/'isolated/Recovery.lean',88),
 'components_prop': (R/'isolated/Realization.lean',29),
 'all_vertices': (R/'isolated/Realization.lean',37),
 'no_leafless': (R/'isolated/Realization.lean',40),
 'absorption_premises': (R/'isolated/FinalWork.lean',167),
 'author_opening': (A/'RESULT.md',3),
 'reviewer_opening': (R/'RESULT.md',3),
 'table_repeat': (R/'RESULT.md',48),
}
located = {k: {'path': str(p), 'line': n, 'verbatim': (ROOT/p).read_text().splitlines()[n-1]}
           for k,(p,n) in quotes.items()}
receipt = {'scope': 'bounded file/count/source-location check only; no Lean replay or new scientific replication',
 'controls': controls, 'manifest_entry_counts': {'author':len(amap),'reviewer':len(rmap)},
 'selected_file_count':len(selected),'selected_hashes':hashes,
 'parsed_counts': {'actual_recover':len(recover),'success':12,'refusal':10,'original_address':len(cert),
                  'alternative_certificates':len(alts),'reference_permutation':2},
 'crossed_target_readout':cross, 'repeated_charge_readout':repeat,
 'named_compiled_records':picked,'source_locations':located,
 'replay_metadata_retrieved': {k:replay[k] for k in ['positive_modules','declaration_count','private_count']},
 'seconds': time.perf_counter()-start}
(BASE/'BOUNDED-EVIDENCE-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'selected_file_count':len(selected),'controls':controls,'parsed_counts':receipt['parsed_counts'],
                  'seconds':receipt['seconds']}))
