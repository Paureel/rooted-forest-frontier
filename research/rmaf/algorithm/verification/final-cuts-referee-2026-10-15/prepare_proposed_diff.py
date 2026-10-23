#!/usr/bin/env python3
"""One-shot exact-text scope proposal; frozen sources are read only.

The toolkit emitall guide was consulted. This task needs a standard unified
diff between sealed prose and replacements, so use difflib without editing input.
"""
import difflib
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[4]
A = 'research/rmaf/algorithm/universal233/final_cut_recovery/'
R = 'research/rmaf/algorithm/verification/final-cuts-2026-10-15/'
replacements = {
 A+'RESULT.md': [
  ("The author Lean proofs establish exact original realization, cost P.length-1, original agreement preservation, and the source-operation bound described below.",
   "Success checks only the source; original target agreement requires the actual premise `agreement T S P = true`, and minimum selection remains open. The author Lean proofs establish exact original realization, cost P.length-1, original agreement preservation, and the source-operation bound described below."),
  ("The final recovery is called once after selecting the final minimum labelled agreement.",
   "The future main caller must select its final minimum labelled agreement and invoke recovery once afterward; that caller remains open.")],
 A+'INTERFACE.md': [
  ("It then calls the unchanged `CoreProgram.generate S (blockColor P) (P.length-1)` and returns its literal first output. It never enumerates set partitions or combines local cut sets.",
   "It then calls the unchanged `CoreProgram.generate S (blockColor P) (P.length-1)` and returns its literal first output. The runtime record contains the partition and original cut addresses; the full component list is a proof witness. `recover` never enumerates set partitions or combines local cut sets."),
  ("The final call occurs once after selection of P.",
   "The future main caller must invoke recovery once after selecting P; its actual call remains open.")],
 R+'RESULT.md': [
  ("| Repeated per-branch recovery has the once-only bill | REFUTED-AT-WITNESS | k=q3,c2,calls8:64>8; explicit false diagnostic |",
   "| Repeated per-branch recovery can omit the invocation factor from the summed exponential charge | REFUTED-AT-WITNESS | k=q3,c2,calls8:64>8; charge multiplicity only, with no tight runtime lower bound or tiny-fixture failure of generous F claimed |")]
}
sealed = json.loads((BASE/'BOUNDED-EVIDENCE-RECEIPT.json').read_text())['selected_hashes']
diffs=[]
for rel, pairs in replacements.items():
    before=(ROOT/rel).read_text()
    assert hashlib.sha256(before.encode()).hexdigest()==sealed[rel]
    after=before
    for old,new in pairs:
        assert after.count(old)==1, (rel,old)
        after=after.replace(old,new)
    diffs += difflib.unified_diff(before.splitlines(True),after.splitlines(True),
                                  fromfile='a/'+rel,tofile='b/'+rel,n=1)
(BASE/'PROPOSED-SCOPE-ERRATUM.diff').write_text(''.join(diffs))
added = ['# Proposed scope additions\n\n',
         'Review-only excerpts from the proposed diff. Frozen reports remain unchanged.\n\n']
for line in diffs:
    if line.startswith('+++ b/'):
        added += ['## '+line.removeprefix('+++ b/').strip()+'\n\n']
    elif line.startswith('+'):
        if line.startswith('+|'):
            added += ['| Claim | Ruling | Source/evidence |\n|---|---|---|\n']
        added += [line.removeprefix('+')+'\n']
        if line.rstrip().endswith('The result is'):
            added += [''.join((ROOT/(A+'RESULT.md')).read_text().splitlines(True)[18:20])+'\n']
(BASE/'PROPOSED-ADDITIONS.md').write_text(''.join(added))
print(json.dumps({'input_files':len(replacements),
                  'exact_replacements':sum(map(len,replacements.values())),
                  'frozen_writes':0}))
