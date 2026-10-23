#!/usr/bin/env python3
"""One-shot, bounded file/quote checks for this reader review; no theorem replay.

Consulted bootloops/tools/README.md and emitall/GUIDE.md. Emitall handles
receipt claim expressions but not this fixed source-hash and literal-quote
ledger. This small local wrapper does only those metadata checks.
"""
import hashlib
import json
from pathlib import Path
import time

ROOT = Path('/Users/paurel/Documents/ChatGPT/bootscience')
OUT = ROOT / 'research/rmaf/algorithm/verification/both-bad-referee-2026-10-15'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def has_quote(text, quote):
    return quote in text

def main():
    started = time.monotonic()
    # Known-answer controls apply only to these literal metadata helpers.
    assert digest(b'') == 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'
    assert has_quote('alpha beta', 'alpha')
    assert not has_quote('alpha beta', 'alpha gamma')
    spec = json.loads((OUT / 'INPUTS-v1.json').read_text())
    author = ROOT / spec['author_manifest']['path']
    seal = ROOT / spec['sealed_manifest']['path']
    pinchecks = []
    for item in [spec['author_manifest'], spec['sealed_manifest']]:
        actual = digest((ROOT / item['path']).read_bytes())
        assert actual == item['sha256'], item['path']
        pinchecks.append({'path':item['path'], 'sha256':actual, 'match':True})
    aman = json.loads(author.read_text())
    sman = json.loads(seal.read_text())
    assert len(aman['immutable_files']) == 560
    assert len(sman['files']) == 557
    expected = {r['path']:r['sha256'] for r in aman['immutable_files']}
    sealedroot = seal.parent
    expected.update({str((sealedroot / r['path']).relative_to(ROOT)):r['sha256'] for r in sman['files']})
    ledger = []
    for item in spec['sources']:
        path = ROOT / item['path']
        data = path.read_bytes()
        actual = digest(data)
        pin = expected.get(item['path'])
        if pin:
            assert actual == pin, item['id']
        ledger.append(dict(item, sha256=actual, bytes=len(data), lines=len(data.splitlines()),
                           sealed_or_author_pin_checked=bool(pin)))
    quotes = []
    sources = {r['id']:r for r in ledger}
    for item in spec['quotes']:
        text = (ROOT / sources[item['source']]['path']).read_text()
        assert has_quote(text, item['quote']), item['id']
        start = text.index(item['quote'])
        line = text[:start].count('\n')+1
        quotes.append(dict(item, line=line, exact_match=True))
    summary = json.loads((sealedroot / 'SUMMARY-v1.json').read_text())
    comparison = json.loads((sealedroot / 'COMPILED-CONTROL-COMPARISON-v1.json').read_text())
    assert summary['compiled_core_receipt_comparisons'] == comparison['core_receipt_comparisons'] == 120
    assert summary['compiled_plan_comparisons'] == comparison['plan_comparisons'] == 100
    assert summary['compiled_executions'] == comparison['execution_comparisons'] == 305
    assert summary['independent_original_return_checks'] == comparison['independent_return_checks'] == 79
    assert summary['exact_rational_mass_comparisons'] == comparison['mass_comparisons'] == 915
    assert summary['actual_callback_occurrences'] == comparison['actual_callback_occurrences'] == 378
    provenance = json.loads((sealedroot / 'PROVENANCE-CHECKS-v1.json').read_text())
    for skey, pkey, expected_count in [
        ('scientific_modules_cold_built','scientific_producers',160),
        ('stored_scientific_occurrences','stored_occurrences',4675),
        ('resolved_scientific_names','resolved_names',4647),
        ('private_occurrences','private_stored_occurrences',418),
        ('generated_recursors','generated_recursors',64),
        ('compiler_auxiliary_names_inventory_only','compiler_auxiliary_names_inventoried',1418),
        ('direct_custom_axioms','direct_scientific_axioms',0),
    ]:
        assert summary[skey] == provenance[pkey] == expected_count
    assert provenance['coalesced_occurrence_excess'] == 4675-4647 == 28
    assert summary['finite_original_refiners_precontact'] == 13650
    assert len(comparison['frozen_callback_mismatches']) == 4
    assert all(r['actual_callbacks'] == [] and r['frozen_expected_callbacks'] == [1]
               for r in comparison['frozen_callback_mismatches'])
    axioms = json.loads((sealedroot / 'AXIOM-INVENTORY-SCOPE-v2.json').read_text())
    fields = ['author_manifest_axiom_summary','author_certificate_all_module_axioms','fresh_full_stored_dependency_axioms']
    assert all(axioms[k] == aman['standard_axioms'] == ['Classical.choice','Quot.sound','propext'] for k in fields)
    record = {'scope':'File metadata and exact quote checks only; no new mathematical, statistical, or kernel replay.',
              'known_answer_helpers':'empty SHA and positive/corrupted literal quote controls passed',
              'pinchecks':pinchecks, 'manifest_entry_counts':{'author':560,'sealed_review':557},
              'sources':ledger,'quotes':quotes,
              'summary_vs_compiled_receipt_counts':'120 core receipts, 100 plans, 305 executions, 378 callback occurrences, 79 returned-forest checks, 915 rational comparisons agree as metadata',
              'summary_vs_provenance_counts':'160 producers, 4675 stored occurrences, 4647 resolved names, 418 private occurrences, 64 recursors, 1418 compiler auxiliaries, 0 direct custom axioms; difference 28. These are receipt fields, not new audits.',
              'S11_q4':'four rows preserve expected [1] versus actual []',
              'axiom_v2':'all three full lists agree with author manifest std3',
              'seconds':time.monotonic()-started}
    (OUT / 'CHECKS-v1.json').write_text(json.dumps(record, indent=2)+'\n')
    md = ['# Source ledger', '',
          'Read extents identify retrieval scope. Hashing a file does not mean its proof body was read or rechecked. All links are local.', '',
          '| ID | Source | Read extent | SHA256 |', '|---|---|---|---|']
    for row in ledger:
        path = ROOT / row['path']
        md.append(f"| {row['id']} | [{path.name}]({path}) | {row['read']} | `{row['sha256']}` |")
    md += ['', '## Literal quotations', '', '| ID | Exact location | Quotation |', '|---|---|---|']
    for row in quotes:
        path = ROOT / sources[row['source']]['path']
        md.append(f"| {row['id']} | [{row['source']}:{row['line']}]({path}:{row['line']}) | `{row['quote']}` |")
    md += ['', 'Manifest identities and inventory counts are in INPUTS-v1.json and CHECKS-v1.json. The full compressed expression archives were not decompressed in this review.', '']
    (OUT / 'SOURCE-LEDGER-v1.md').write_text('\n'.join(md))
    print(json.dumps({'source_files_checked':len(ledger),'exact_quotes_checked':len(quotes),'seconds':record['seconds']}))

if __name__ == '__main__':
    main()
