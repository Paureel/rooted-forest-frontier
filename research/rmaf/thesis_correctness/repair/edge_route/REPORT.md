# Original-edge adversary result

The finite search found no counterexample to root-safe normalization under the tested active-state premises. Four frozen controls and four corruption checks passed before the algorithm source was opened. The universal normalization theorem remains open; no proof was constructed during this adversary phase.

## Executed counts

| Class | Inputs or candidate states | Checked states | Normalization premises | Root premises with >=2 removed cuts | Failures |
|---|---:|---:|---:|---:|---:|
| Actually reached, five leaves | 1,000 inputs | 178 root snapshots | 2,910 | 1,230 | 0 |
| Actually reached, six leaves | 1,000 inputs | 364 root snapshots | 9,260 | 4,354 | 0 |
| Structural, all three-leaf source-mask states | 9,216 candidates | 285 | 1,356 | 300 | 0 |
| Structural, four-leaf sampled source-mask states | 10,000 candidates | 214 | 951 | 297 | 0 |

The reached search observed 60,952 snapshots and retained 18,074 distinct source/snapshot combinations. Of these, 542 had a common active subtree pair whose LCA was an unlabelled component root. Every candidate expansion and containment check passed. The checker enumerated 24,036 active original-edge cutsets in those 542 states, including 21,229 agreement-forest cutsets. Exactly 5,584 tested premises had an absent LCA parent and at least two removed path edges. All 5,584 used nonoptimal cutsets; the search provides no optimal-cutset root examples.

The structural search is separate. It examined 19,216 source-mask combinations, of which 8,897 satisfied containment and 499 had a connected common sibling pair suitable for further checks. Only the three-leaf source-mask census is exhaustive. The four-leaf sample uses seed 615 and retains the generation parameters in its receipt.

## Reached example

Take unary-rho trees `T1=(a,((b,(c,d)),e))` and `T2=((((a,b),e),d),c)`. With initial budget 2, the actual generator first cuts the incoming edge of the T2 cluster `{a,b,e}`, contracts the common `{c,d}` subtree, cuts its incoming edge, and finishes that component. The active F1 is `rho -> (a,(b,e))`; active F2 consists of isolated `rho` and the unlabelled-root tree `((a,b),e)`. The completed `{c,d}` component is retained when verifying the expanded forests against both original inputs.

For the sibling pair `(b,e)`, the F2 path has original edge IDs `{4,6,7}`; ID 4 enters `{a,b}`, ID 6 enters `b`, and ID 7 enters `e`. Choose `E={4,5,6}` and `E2={5}`, where ID 5 enters `a`. The two removed path edges are `{4,6}`, and their LCA is node 3 with no parent. Root-safe normalization gives exactly `E'={5}`. The original labelled blocks are `{a},{b},{c,d},{e},{rho}`; the normalized blocks are `{a},{b,e},{c,d},{rho}`. Both are AFs of the active forests and the original trees, and the normalized cut count is one rather than three.

The complete witness includes the original source graphs, expanded forests, active graphs, contraction/finishing/cut histories, protection sets, active edge IDs, original path segments, `E`, `E2`, `E'`, and all component blocks. A separate self-replay of this JSON passed thirteen exact checks. The self-replay is not a fresh-author verification.

## Method and limits

The checker deletes graph edges by their original bottom-node identifiers, obtains labelled components, and compares rooted induced shapes and minimal embedding vertices in each source forest. It tests component containment explicitly. Every active cutset is enumerated separately, including different cutsets that yield equal labelled partitions. For each E it searches subsets E2 outside the selected path until the common sibling premise holds. It then removes every E-cut on the path, adds the LCA-parent edge only when at least two path cuts were removed and that parent exists, and checks AF preservation, nonincreasing cut count, and retention of E2.

The original algorithm is used only to generate reached states. Its cut, reduction, and shape methods never decide whether a candidate is an agreement forest. The checker expands contracted atoms and restores completed components with original source vertices, then independently checks both forests against their original trees. Enumerated E remains restricted to edges present in the active snapshot. The source-generator dependency and checker hash are retained in each main receipt; no sibling `component_route` work was read.

I read printed pages 12–18, 101–103, and 112–116 of the supplied Whidden thesis. The active containment hypothesis comes from page 17 and is necessary for interpreting the page 101–103 normalization claim. Page 113's second `(x,u)` exchange still needs a theorem with the root case and exact consumer hypotheses. This adversary search does not establish global correctness, marked-state transport, common-subtree transport as a theorem, runtime bounds, or conversion from unary-rho conventions.

## Local records

- Summary: `/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/results/thesis-correctness-repair-edge-summary.json`
- Reached witness: `/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/edge_route/first-reached-root-witness.json`
- Checker: `/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/edge_route/adversary.py`
- Source, provenance, and timing notes: `/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/edge_route/SOURCE-NOTES.md`
- Dashboard checkpoint: `/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/progress/thesis-correctness-repair-edge.json`

The main runs used `./bootloops-python` with `run_reached.py --n 5 --limit 1000`, `run_reached.py --n 6 --limit 1000`, `run_structural.py --n 3 --limit 0`, and `run_structural.py --n 4 --limit 10000`. Those scripts are in the same local edge-route directory. No Lean theorem was attempted before this adversary result; a distinct original-edge proof construction requires the next authorization from the parent.
