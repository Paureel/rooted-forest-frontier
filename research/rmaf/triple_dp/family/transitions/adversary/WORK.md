# Independent merge adversary workfile

Started 2026-10-14. Owned by the merge_adversary arm. Target read first from
`../TARGET.md`; no author checker or merge proof code consulted.

Scope: pin an independent undirected graph/path family checker, independently
validate frozen fixture expectations, run plants and a timed pilot, then a
small bounded adversarial enumeration. Retain every actual witness unchanged.
No universal-proof claim and no census-as-proof claim is permitted.

Status: initialized; frozen controls and methodological instructions next.

## Provenance pin

The two local checker methods will share only the frozen target/fixtures,
Python standard library, basic string-tree representation and this author.
Route G uses explicit undirected graph paths; route P uses prefix/LCA paths.
They are algorithmically distinct but NOT a fresh-author certification.
Fixture values will not be regenerated or altered to fit either route. Any
mismatch is a stop condition. Independent fresh-author review remains outside
this arm. A deliberately mismatched comparison and a broken-checker copy are
required before bounded evidence is reported.

## Frozen control contract

The inherited controls contain 5 positives, 4 malformed inputs, 4 incorrect
numeric propositions with clean twins, and 3 corrupted supports with clean
twins. Every item must execute and its result and exact diagnostic be saved.
T1 is the zero-closed-cost null. A broken copy that ignores numeric claim
mismatches must be detected by the frozen battery. Any valid-input merge
failure stops bounded search immediately, retains the exact witness and is
reported as FIRE; malformed controls cannot be counted as theorem fires.

## Timing plan

No runtime estimate yet. The first execution will be the controls and a
small deterministic pilot with explicit case denominators, warm-up marked,
and monotonic timings. Main bounded search launch depends on a measured
projection. Progress means fully checked valid family pairs saved in the
receipt; no acceptance inference from process exit or CPU activity.

## Source audit after checker pin and implementation

Read `cost_route/FamilyAssembly.lean` lines 11–26, 58–79 and 98–103:
`finite`, `bounded`, `convex`, `labelled`, `disjoint`, `covers`, `boundary`,
`root_spec` are exactly the family obligations. Cost is literally
`f.blockCount - boundaryCharge f.boundary`; counting nonboundary indices
agrees on validated duplicate-free, complete families. The graph checker
implements no extra full-vertex-coverage or minimal-hull assumption.

Read `ConnectedRegions.lean` lines 7–11: `OnPath` is the prefixes from LCA to
either endpoint, and `PathConvex` requires them all. This agrees with the
separate prefix route; BFS is a separately executed representation, not a
kernel-certified correspondence. `FamilyAssembly.lean` line 5 explicitly
permits repeated labels. `FamilyModel.lean` lines 35–37 define a different
`LabelledTree` with distinct labels, which is NOT imposed here. No old
receipts, checker scripts, or new merge proof source have been opened.

Before first control evaluation, add supplemental index-list, out-of-tree,
root-owner, exact-retention, repeated-label and tagged-name controls. These
are separate from and cannot alter the inherited frozen 5/4/4/3 suite.

## Executed outcome

Controls passed before pilot. Numeric-blind copied checker was detected;
its control subprocess exited 1 and retained exact failing diagnostics.
Pilot checked 124 pairs, then a saved timing/source-hash gate admitted the
192-pair bounded run. No valid-input merge failure or checker disagreement
occurred. All source and receipt files are preserved.

Verbatim main-driver summary:

```json
{"checked_pairs": 192, "controls": {"malformed": {"passed": 4, "total": 4}, "positive": {"passed": 5, "total": 5}, "supplemental_malformed": {"passed": 4, "total": 4}, "supplemental_positive": {"passed": 1, "total": 1}, "supplemental_retention": {"passed": 2, "total": 2}, "support_corruption": {"passed": 3, "total": 3}, "wrong_result": {"passed": 4, "total": 4}}, "elapsed_seconds": 0.03618937499959429, "receipt": "results/triple-family-transitions-adversary-bounded.json", "verdict": "NO-FIRE-BOUNDED"}
```

Acceptance-gate assessment: exact finite arithmetic needs no decimal
precision ladder or fitted-anchor exclusion. No fitting or threshold tuning
occurred. The earlier control/specification pin supplies the declared test;
positive, negative and checker-mutation runs were executed. A second
algorithm agrees; same authorship and shared semantics are explicit. Thus
the bounded observation is reportable, while universal closure and
fresh-author certification remain OPEN. REPORT.md has the scoped claims and
replay instructions. Two prose/number passes checked source locators, units,
control denominators and pilot/main overlap; no novelty claim is made.
