# Actual consumer trace

All three improved-algorithm milestones remain OPEN. Table entries are
conditional consumer requirements, not grants of their graph hypotheses.

## Source records read

| Read claim | Exact record locator | Copied load-bearing source text |
|---|---|---|
| Pure exchange needs its entire rest state | `pure_bridge/FORMAL.md:11` | “All existing marks and all remaining interactions are included in `restValid`.” |
| Pure graph interface remains open | `pure_bridge/FORMAL.md:33` | “G1–G7 have not been connected to the Lean exchange structures.” |
| Query budget must include regions | `pure_bridge/FORMAL.md:17` | “`role_swap_parameter` proves that this residual is at most `d` if `h≤d+r−1`.” |
| Triple admission is componentwise | `triple_dp/PROOF.md`, Statement and conventions, paragraph 1 | “Every source component D is either isomorphic to T restricted to its labels, or has exactly three labels.” |
| Triple terminal action is conditional | `triple_dp/PROOF.md:70` | “Conditionally on G1–G3 and a correct baseline branching scheme, an existing recursion node in this class becomes a polynomial terminal test” |
| Executable model is not graph closure | `lean/FORMAL.md:70–72` | “They do **not** finish formal equivalence to the paper's graph-theoretic definition.” |

These are retrieved source statements; the candidate design and finite
witnesses below are newly constructed/development measurements. No prior-art
or novelty statement is made.

## Call sites and obligations

| Actual executable call | Enforced hypothesis | Further proof required | Receipt/provenance |
|---|---|---|---|
| B1 `select_core` / `core_children` | Shared target vertex; ≥2 touching colors; degree three in at least one; every touching component target-compatible; each split has actual r−1 source-edge certificate | All optimal completions refine some emitted color-retention branch; suppression/restriction transfer; universal multi-color cost/mass; termination | `algorithm-cover-core-controls-v1.json`: two synthetic compatible cores only, explicitly supplementary; no hard-child reachability |
| B1 `fallback` | Integer nonnegative budget; correct target/source label partition | Budgeted cut enumeration represents every feasible forest; source cut/suppression semantics | B1 27 controls and pilot; same graph author/primitives |
| B2 `frontier(first_only=True)` | Actual source cut states; every child is compatible/triple | Safe coverage **refuted** in the finite executable model and measured graph fixture | `algorithm-cover-minimum-witness-v2.json`; `FailedFrontier.lean`, ten route-author audited statements |
| B3 `frontier(first_only=False)` / `full_minimal_cover` | All actual source cut sets within q enumerated; charge equals labelled-component increase; dedup by partition; only strictly coarser terminal states dominate | Full graph cut realization; component restriction/suppression; every optimum reaches some minimal retained ancestor | `algorithm-cover-full-pilot-v3.json`, two development fixtures, original fallback retained |
| B3 `solve` on each retained child | Remaining budget exactly q−d; all child labels represented | Same explicit fallback obligations; no terminal-library import | Full pilot records every attempted local budget and cut-set count |
| `reconstruct_sources` | Returned original-source minimal spans directly checked disjoint; all labels covered | Multi-source BFS regions remain connected; boundary cut count p−m; general graph semantics | Original-source cut reconstruction checked on every accepted control/pilot output |
| Pure-bridge library | **No actual calls**: `library_calls=0`; membership/query ledger only | G1–G7 at FORMAL lines 25–31, joint marks, whole-state `clearRest`; exact marked minima and region-adjusted query budgets | Conditional library intentionally disabled; no release receipt imported as graph closure |
| Triple library | **No actual calls**: explicit cut enumeration substitutes | G1 at PROOF line 23, G2 line 46, G3 line 48; arbitrary-depth implementation; independent implementation release | Conditional library intentionally disabled; no family/restriction or degree-two release assumed |

## Universal status and fallback accounting

The proposed full-cover proof follows a feasible optimum's source cut set
to a terminal partition, then to a minimal terminal ancestor. That argument
is OPEN until its graph correspondence and residual-budget transfer are
formalized. The original source-state fallback remains a charged action
whenever the experimental cover finds no feasible child.

The total executor therefore has an explicit defined action on all admitted
inputs and a finite termination argument in prose, but no universal Lean
algorithm theorem or O*(c^k) result. In particular, B1's initial single color
offers only the full-budget original local problem. B3 pays every cut-set
test and every retained state; its five-leaf vector has mass >1 at both
231/100 and 23391/10000. A larger one-level terminal mass rejects this
specific recurrence certificate, not every possible global analysis.

No statistical fit was run. No integral, external engine, deployment,
upload, or toolkit mutation occurred. The parent task owns any shared
BootLoops suite run. Fresh nonauthor graph reconstruction and Lean replay
remain pending; route-author hashes/audits are retained separately.
