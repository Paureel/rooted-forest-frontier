# Cheap/high X0 report

The five fixed, in-regime pair fixtures produced no counterexample. This is a finite NO-FIRE, with the binary-pair query-cost consumer still OPEN. In particular, an unavoidable extra cut has not been converted into a reduction in the worst-case work of every capped query.

## Executed evidence

The initial target was read before the workfile skeleton was written. Fixture expectations were then stored in `sol-fixtures-v1.json` before instrument execution. All Python ran through `./bootloops-python`; all files are local to this x0 directory. No G/E proof, other checker implementation, active composition/restriction/runtime proof, child agent, author contact, or outside compute was used.

| Execution | Completed denominator | Evidence file |
|---|---:|---|
| Planted arithmetic/graph/program controls | 25 of 25 checks | `sol-controls-v1.json` |
| Measured actual-pair pilot | 1 of 1 fixtures; 40 of 40 checks | `sol-pilot-v1.json` |
| Remaining fixed actual-pair battery | 4 of 4 fixtures; 159 of 159 checks | `sol-battery-v1.json` |
| Literal Lean/Python generator comparison | 82 of 82 complete receipts | `sol-literal-comparison-v1.json` |
| Deliberate source-partition corruption | 4 of 4 checks | `sol-outscope-result-v1.json` |
| Literal replay of that corruption | 16 of 16 complete receipts | `sol-scope-literal-comparison-v1.json` |

The actual-pair pilot took 0.00621925 s and the remaining fixed battery took 0.038802083 s. The five fixtures have 7–9 leaves and singleton C. Their complete-budget lists contain 16 raw occurrences and 76 local block queries. The agreement oracle checked 630 partitions refining P and 378 partitions refining raw outputs. These denominators describe different calls and are not counts of distinct whole-input partitions. All 82 budgeted Lean receipts retain 72 emitted occurrences in total; no duplicates were removed.

The graph evaluator is new. It computes original embeddings by address-path unions, rooted restriction topology by projected descendant-cluster sets, literal cut components by graph traversal, and agreement refinements by set-partition enumeration. The source generator is a disclosed transcription of the literal Lean definitions. The exact optimum enumerator is a testing instrument only. Its values are not an algorithmic subroutine, proof, or complexity certificate.

## Fixed pair results

All five fixtures passed every printed ordinary-label, proper-source-partition, overlap, C-clear, original-edge, nonempty-sector and mutual-clear guard. Every emitted raw partition was also checked against the actual components after its literal original source cuts.

| Fixture | LA costs | LB costs | Additional cost after each LA output | Additional cost after each LB output |
|---|---|---|---|---|
| surrounding-A-good-sectors | [3] | [4,4] | [2] | [1,1] |
| surrounding-A-right-attachment | [3] | [4,4] | [2] | [1,1] |
| cheap-bad-A-sector | [3] | [4,4] | [3] | [1,1] |
| both-high-crossed | [4,4] | [4,4] | [2,2] | [2,2] |
| public-good-A-conditional-E | [3] | [4,4] | [2] | [0,0] |

The costs in the last two columns are exact optimum further cuts among agreement partitions refining that raw output, not running times. Original trees, partitions, color maps, cut lists, counters, all query minima and minimizing partitions are retained in the JSON files.

For the public good-A fixture, the minimum among partitions refining P is five components, and the minimum with A whole and B sectors cleared is also five. The first calculation enumerated 30 refinements of P, of which 10 were agreements. The second enumerated eight refinements of the more restrictive partition, of which six were agreements. This reproduces the printed minimum with a smaller search domain than the public pin's 877 all-partition denominator; it is not a replay of that enumeration. Both actual B-clear raw outputs are already agreement partitions. The alleged single original source cut making whole B sectors was rejected.

## Item 4

The primary hostile fixture is

```
S = (((1,(2,((4,6),(5,7)))),3),8)
T = (((1,(4,5)),((2,3),(6,7))),8)
P = {1,2,3} | {4,5,6,7} | {8}
e = 00
A1 = {1}; A2 = {2,3}; B1 = {4,5}; B2 = {6,7}.
```

A is bad: S restricted to A is `((1,2),3)` and T restricted to A is `(1,(2,3))`. Both A sectors are good. The source edge at address `000` gives the two A sectors, so the exact local A cost is one. A is not an original source clade in this fixture; B attaches within the A embedding.

The cheap A output has raw partition `[[2,3],[4,6,5,7],[1],[8]]` and raw cut list `[0,0011,000]`. The two B-clear outputs are:

```
partition [[6,7],[5],[4],[8],[1,2,3]]
cuts      [0011,001110,001100,1]
A remaining cuts = 1; total remaining cuts = 1

partition [[4,5],[7],[6],[8],[1,2,3]]
cuts      [0011,001111,001101,1]
A remaining cuts = 1; total remaining cuts = 1
```

Across the two in-regime fixtures satisfying item 4's antecedent, all four B-clear raw outputs retained A whole. Across all five fixed fixtures, none of the 10 complete-budget B-clear outputs split A. Therefore this finite battery does not decide whether an in-regime split-A output can occur; that universal quantifier remains an explicit obligation.

The deliberately corrupted source

```
S* = (((((1,(4,6)),(5,7)),2),3),8)
```

with the same target, P and e passes every regime guard except source embedding disjointness of P. Its LA costs are [3] and its LB costs are [5,5,5,5]. Its first B-clear output is

```
partition [[6,7],[1],[5],[4],[8],[2,3]]
cuts      [000,00000,00010,000010,1]
A blocks  [[1],[2,3]]
A remaining cuts = 0; total remaining cuts = 0.
```

The four remaining A costs are [0,1,0,1]; two outputs split A. This is an exact failure of an extension that drops the source-partition disjointness hypothesis, and demonstrates that the split-A detector can distinguish zero from one. It is outside the printed regime and does not change the target. A claim that retained unresolved A cost follows merely from four colors, a cheap LA, and a bad A would be false.

The required scoped statement is still the original proper-source-partition version: prove from the actual generator that every B-clear output preserves A whole, or supply an explicit paid/unpaid cut identity for every fragment of A and recompute the envelope. Declaring all output parents whole, or silently using an optimum oracle, would not meet this obligation.

## Mass and query work

The arithmetic controls recover exact masses 1/8, 1/8, 0, 3/16 and 1/4 for [3], [4,4], [], [3,4] and [3,3]. The latter two fail the allowance; deduplicating [3,3] was detected. The high twin attains `2/c^4` and rejects the false bound `1/c^4`. Identical restricted pairs have zero additional cuts, including the actual good-A post-core outputs, so a mandatory positive-progress claim was rejected.

Conditional on the admitted d>=3 and dyadic allowance, a cost-three occurrence exhausts all positive mass. When every d>=4 and c>=2, the elementary inequality is

```
sum c^(-d) = sum 2^(-d) (2/c)^d <= (2/c)^4 / 8 = 2/c^4.
```

The mixed raw lists [3] and [4,4] in the actual fixtures have combined unadjusted mass `(c+2)/c^4`. At `c=233/100` this is `433000000/2947295521`, exceeding `4/c^4 = 400000000/2947295521` by `33000000/2947295521`. Thus the raw lists alone do not give the proposed residual envelope. Item 5 explicitly conditions its claim on the recursive consumer, so this arithmetic obstruction is an unproved-consumer requirement, not an in-regime FIRE against a proved query procedure.

The endpoint-plus-residual arithmetic is exactly `2929867400/2947295521`, with positive slack `17428121/2947295521`, if the residual envelope is first established. These numbers do not establish an algorithm or exponent.

An exact further-cut minimum >=1 states a property of successful completions. It does not show how to answer a capped query at budget b with work bounded by the generic budget-(b-1) cost. The real consumer must specify every query and allocation, rejected and zero-cut calls included, and charge the algorithm that discovers or explicitly removes the needed cut.

## Next consuming statement

A sufficient next theorem must name a residual budget b at entry to the clear generator and charge every literal occurrence of cost d. It must construct any known one-cut A completion from actual original edges and good-sector certificates, and prove how to combine that completion with every B-clear output under the printed source-partition hypotheses. If A is whole, a procedure that outputs its known completion can pass budget b-d-1 to the remaining components; the procedure and its cost must be supplied. If A is split, its already paid cuts and remaining contribution must both be recorded, without charging the same unit twice.

The cheap branch with an unknown bad sector needs a separate efficient query argument: badness alone supplies a lower bound, not a discoverable free cut. Multiple local queries, budget allocations, setup, reconstruction, pruned prefixes and duplicate raw occurrences must fit the claimed bound. Conditional E and the reviewed source-core hypotheses must be supplied at their exact interfaces. No argument of this kind was constructed or certified here.

The complete algorithm, exactness, and exponent milestones all remain OPEN.

## Reproduction and limits

Run the three fixed stages with `./bootloops-python research/rmaf/algorithm/pair_case/cheap_high/x0/sol-evaluator-v1.py controls`, then `pilot`, then `battery`. Run `sol-run-outscope-plant-v1.py` for the negative scope control. Literal Lean sources and output JSONL are under `sol-lean`; comparisons are reproduced by `sol-compare-literal-v1.py` and `sol-compare-scope-v1.py`.

The original RMAF source hash is `4960d5be9a5f1eb6b15d11c76130bee5263125631314a4eb2d43d500d5b513a9`; CoreProgram is `9aa92355dfecf6e0e3d7707c1c284cabcb2f3846b6682e3b55b719e35cb7311f`. CoreProgram was freshly compiled without source changes. Its imported existing CoreGraph binary hash is `aff56e97a347d290c9e4ce717d1d011fd4dafeacf302a145ff28053019527b7a`; the RMAF binary hash is `a79a93f29f27daadde45c4985478060ce176404eb282083f68b1bc3242ffa61d`. The existing build's RMAF source matches the original source hash. This arm did not review or reconstruct the CoreGraph proof dependency.

The first compiler launch through the elan shim failed because it tried to create `/Users/paurel/.elan` outside the writable roots; using the bundled native Lean binary resolved that limitation. The first replay wrapper lacked `import Lean` for JSON and failed compilation; the original wrapper and diagnostic are retained, and the corrected wrapper then executed. Neither failure changed any fixture expectation or mathematical output. No upstream source, integrity pin, frozen result, or alpha registration was changed. The general toolkit validation suite and universal proofs were not run; this arm changed no toolkit code and makes only the scoped finite report above.
