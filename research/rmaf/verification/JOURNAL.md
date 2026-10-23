# Fresh edge-cut verification

## Boundary and birth record

2026-10-14. The initial target read was `research/rmaf/spec.json`. No oracle,
branching, or decomposition implementation or argument has been read. This
arm independently enumerates edge deletions, discards leafless components,
and suppresses unary vertices. It will intersect complete forest catalogues
to obtain exact minimum component counts. The common mathematical layer is
the rooted agreement-forest definition; Python's runtime is also shared.

## Frozen controls

Pending: explicit hand-derived controls, failure criteria, and a deliberately
wrong comparison must be written before corpus results are inspected.

## Pilot and computation budget

Pending: measure n=3,4 enumeration before deciding whether all n=5 pairs fit.

## Implementation freeze

Pending: retain SHA-256 of implementation before reading any external results.

## Exact evidence

Pending: run controls, then finite corpus, retaining witnesses and counts.

## Comparison and contact log

Pending: after implementation freeze and execution, compare result data only.
Any corpus used by candidate discovery cannot serve as held-out certification.

## Semantic audit

Pending: inspect formal definitions/certificates only after independent code
has been frozen. Compilation will not substitute for this review.

## Verdict

OPEN. Finite checks are not a universal correctness or improved-bound proof.

## Executed pilot and freeze

Controls were frozen in `verification/controls.json` before running the evaluator.
All five hand-optimum controls, three malformed-input controls, and the planted
wrong integer comparison produced the specified outcomes (9 controls).
The n=3 pilot took 0.000129333 s for 6 pairs; n=4 took 0.002217792 s
for 120 pairs, including 0.001831959 s to catalogue 15 trees with 64 masks
each. All n=5 has 105 trees with 256 masks and 5,565 unordered pairs.
The measured n=4 work multiplied by 28 for edge-mask count and 46.375 for
pair count gives a subsecond projection, assuming modest per-mask growth.
This projection is only for n=5; its actual time will be retained.
Real progress is the retained exact pair count in verification-corpus.json.

Implementation frozen before accessing any oracle data: SHA-256 `8b192eeafd55338efdd9b233ab6d19e69269368237e33572b7c464e186c3f234`.
Fixture SHA-256 `f286236779308232e32d6400bd891165b985fed8edbd46779f00101a9b402d31`.

Deepest shared layer: the mathematical no-rho rooted-MAF definition and Python
runtime. Different forest-generation algorithms and separately authored code
reduce a shared embedding-check error; they cannot remove a shared definition
error, so semantic definition review remains necessary.

## Result data access and comparison registration

After the frozen edge-cut implementation had executed all n=3..5 cases, the
result-only oracle-corpus.json and oracle-controls.json files were opened for
schema inspection. No discovery source or arguments were read. Before the
comparison runs, any unequal optimum, missing/extra generated tree, or unequal
complete set of optimum leaf partitions is registered as a failure.
The controls already demonstrated rejection of a planted unequal integer pair.
The entire discovery corpus is now in the contact log and is not held-out
evidence for algorithms developed from it.

## Comparator destructive controls (registered before running)

The result-ingestion comparator must reject each one-at-a-time plant: change
one optimum k to k+1; replace one optimum forest with the empty partition;
remove one pair row. Each plant uses an isolated copy of the n=3 oracle data
with no evaluator changes. Its uncorrupted n=3 twin must pass. Expected exit
code is 1 for each plant and 0 for the twin. The comparator must also require
all m^2 ordered pairs exactly once in each supplied batch.

## Executed finite verdict

`./bootloops-python research/rmaf/verification/edge_cut.py --max-n 5`
retained 5,691 unordered pairs. The n=5 phase took 0.085020458 s, including
0.059301667 s for 105 edge-cut catalogues.

`./bootloops-python research/rmaf/verification/compare_results.py` printed:
```
{"status": "finite-agreement", "ordered_pairs_checked": 11259, "seconds": 0.2039859999995315, "discrepancies": []}
```
The comparison included every ordered n=3,4,5 pair, exact optimum k, and the
complete set of optimum forest leaf partitions. No differences were found.
`plant_comparison.py` accepted the clean twin and rejected wrong-k, wrong
partition, and missing-pair copies with exactly the registered exit codes.
Evidence is in verification-comparison.json and verification-plants.json.

VERDICT: finite independent-route agreement. No universal new-rule correctness,
all-size optimality theorem, or improved exponential-base claim follows. These
results cannot certify later discovery algorithms as held-out tests.

## Formal control audit executed

After the frozen evaluator had finished, lean/RMAF.lean was read for semantic
review. FORMAL-AUDIT.md records open interface obligations and the finite
versus general theorem boundary. `audit_formal_controls.py` independently
computed k=2 and minimum k=3 when either cherry endpoint is isolated, rejecting
the overlapping-pair forest. The complete optimum set is the single partition
{a,b,d}|{c}, with raw cut masks retained in verification-formal-controls.json.
The generic formal optimality statement is accurately scoped to executable
assignments; semantic equivalence, input well-formedness, relabeling, existence,
and faster running time remain open.
