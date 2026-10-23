# Source generator implementation work

The frozen source generator has a complete standalone source-operation bound, with the arbitrary color-function cost explicit. The result combines a mathematical correspondence to the actual source operations with Lean proofs of receipt equality, size/helper charges, receipt-list copying, pruned calls and the final budget-capped bound. Fresh nonauthor source-cost review remains pending. The complete exact faster rooted-MAF algorithm and all three main milestones remain OPEN.

For n input leaves, N=2n−1 tree constructors and B=min(q,n−1), the non-oracle source work is at most

    128(N+1)^3 + (256((N+1)(N+2))^3+6)(B+1)2^(B+1).

This gives O((n+1)^7 2^B). The bit-operation version is O(H(n+1)^7 2^B + input encoding length + sum of actual color-evaluation costs), where H includes large labels, returned colors, the input budget and B+O(1)-bit receipt counters. The literal conversion makes n source color calls on accepted labels and zero on duplicate-label refusal. A finite table with at most five stored colors gives a polynomial external lookup cost. See COST-MODEL.md for the finite source-charge argument and RAM interpretation.

The actual metered evaluator projects to the immutable `generate` for every input. Normalization and erase cannot increase current constructor/payload/address footprint. Actual detached states, including the final attempted overbudget children, have polynomial volume. Normalization/group append, quadratic find-filter-length work, erase/address comparisons, output partition construction, fixed Nat counter operations, root/duplicate/erase refusals, zero-budget work and actual left output/refusal-list copy lengths are charged. Repeated copying contributes the retained B+1 factor.

Canonical author replay: `results/algorithm-universal233-core-work-20261015T081612Z/certificate.json`.

- 20 exact copied source modules rebuilt locally in 13.828745 seconds.
- 1,718 actual module-origin declarations audited, including generated/private declarations; observed axiom union: Classical.choice, Quot.sound, propext.
- 12 positive controls passed. Unit-time append, suppressed pruned work and hidden oracle-call propositions all failed exact Lean checking.
- Missing-record corruption and an isolated custom-axiom plant were caught.
- Entire replay, including controls and audits: 27.146006 seconds.

The failed development replays remain retained. The first passing development receipt used the weaker guard allowance and is superseded by the canonical receipt. The canonical frozen dependencies were checked against the final source-coverage manifest before and after replay. No upstream/frozen source was changed, and no cut-realization work was inspected.

The first remaining runtime consumer is the ownership-prefix caller's construction of its finite color table and its sum of the actual `generate` bound over all prefixes/remaining budgets. That consumer must also charge the subsequent pair/refinement procedures and prove the complete exact runtime below 2.3391 under ordinary q=k−1 with no implicit rho. A fresh reviewer must first check the finite source-operation correspondence and initialization constant; the replay alone does not certify machine-instruction complexity or full algorithm integration.
