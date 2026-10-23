# Fresh referee audit of CASE-ARGUMENT-v1

Status: bounded no-fire on the intended edge-induced binary claims. No in-scope counterexample or HIGH-severity defect was found. The universal claims remain OPEN at their stated interfaces. CASE and RESULT are unmodified.

## Scope and sources

The initial reads were CASE and RESULT only. This reviewer authored neither, read no sibling integration/search/adversary/safe-cover work, and performed no literature search. Subsequent sources were project AGENTS, the applicable project skills, `bootloops/tools/README.md`, and the permitted existing `algorithm/x0/README.md` and `fresh_oracle.py`.

CASE locators refer to SHA-256 `c9cb372017192576e5d08f12863cec26085fb207bd3abc05b59bc24e98a070fb`. Read claims and reviewer inferences are separated below. The source trace, coverage, history, selector/exchange formalization, exact decomposition, complete solver and runtime were explicitly OPEN in CASE 3, 24, 32, 52 and 64; they are not treated as undisclosed defects.

## Audience table

The methods invoke tree geometry, agreement forests, branching recurrences and Lean. Solver implementers and incumbent-method/general readers also receive rows. Novelty rows audit framing only; no priority assessment was performed.

| Audience | Standard objection | Axis | Answer location | Severity | Minimal repair; CASE/RESULT unmodified |
|---|---|---|---|---|---|
| Tree/AF theorist | Which rooted source edge splits the crossing final B block? An arbitrary coloring does not supply one. | Correctness | CASE 9, 22, 46–50: selector supplies an edge; surgery concerns an agreed final block. Orientation is implicit. | MEDIUM precision | Define `e=(u,v)`, descendant labels D and colors by D/complement; transfer the proper cluster `Q∩D` inside final block Q. |
| Tree/AF theorist | How does this compare with existing good-component exchanges? | Novelty | RESULT 11 makes no novelty claim. | LOW | Defer priority claims to a sourced review. |
| Algorithm analyst | Are the other parents' costs paid once, and are unresolved lower bounds actually two? | Correctness | CASE 36–42; exact decomposition remains open at 64. The all-p inequality is unstated at 38. | MEDIUM exposition | Define the post-core budget q, exact resolved costs and lower bounds; include the calculation below. |
| Algorithm analyst | Does conditional mass below one establish a new exponent? | Novelty | CASE 3, 32, 64; RESULT 3: exponent OPEN. | LOW | No change needed. |
| Formal-methods reviewer | Do the Lean checks cover selector/exchange/source grammar? | Correctness | CASE 3, 24, 52, 56, 64; RESULT 7, 11 explicitly distinguish them. | LOW | Preserve that theorem/scope distinction. |
| Formal-methods reviewer | Is a full new algorithm theorem claimed? | Novelty | RESULT 3, 11 decline it. | LOW | No novelty assessment. |
| Solver implementer | Can restricted cuts be lifted through suppression and attributed to the correct source parent? | Correctness | CASE 36, 40, 50 require actual cuts/namespaces; 64 leaves history/lifting open. | LOW, expressly OPEN | Require the original-edge witness described below. |
| Solver implementer | Is a general faster solver available? | Novelty | CASE 3, 64; RESULT 3 say it remains OPEN. | LOW | No change needed. |
| Incumbent/general reader | Does RESULT's “It reduces” imply the universal reduction is established? | Correctness | RESULT 3 first labels the result conditional; 11 and CASE 3 identify proposed universal arguments. | LOW | Prefer “It proposes a reduction” in RESULT 5. |
| Incumbent/general reader | What advance over current rooted-MAF methods is claimed? | Novelty | RESULT 11 makes no novelty claim; CASE 3 declines a new runtime. | LOW | Retain this scope until solver and literature work are complete. |

## Bounded exact checks

Before execution, the planned controls, literal-case checks and failure conditions were written here. The fixed tests demanded correct identical-tree output, rejection of wrong rooted topology and a corrupted optimum, clearance on every intersection edge of one example, a valid exchange without a component increase, and equality of unrestricted/A-retained optima. Additional fixed controls covered root promotion, one-cut local completion and query accounting. No census was authorized or run.

I used the existing X0 instrument through the retained one-shot `referee_case_checks_v1.py`. The controls ran first, then the case, using `./bootloops-python`. Their measured times were 0.000171 and 0.006104 seconds. The toolkit index has no matching rooted-MAF instrument; this wrapper adds no generic capability.

The synthetic local example is

```
S=(((1,2),((3,5),(4,6))),7)
T=(((1,(3,4)),(2,(5,6))),7)
A={1,2}, B={3,4,5,6}, C={7}.
```

Both parents have two occupied regions at shared target vertices `0,00,01`; both intersection edges satisfy both clearance tests. The wrapper separately computes occupied regions and induced-span degree. Promoting the six-leaf target makes its original root an internal shared vertex and preserves clearance. Singleton C and untested admission guards exclude interpreting this example as a tidied global scaffold state.

The valid partition `{1}|{2}|{3,5}|{4}|{6}|{7}` exchanges to `{1,2}|{3}|{5}|{4}|{6}|{7}`, preserving six components. Literal five-edge source witnesses share four cuts; A edge `00→000` is replaced by B edge `010→0100`. Unrestricted and A-retained optima both have five components, each over 877 tested partitions (`case.json`, original/exchanged partition and source-cut fields, both optimum fields).

Controls rejected wrong rooted topology and a corrupted optimum; identical three-leaf trees gave one component. The bad local triple `S=((1,2),3)`, `T=((1,3),2)` has optimum one further cut, realized by source edge `0→01` producing whole agreed colors `{1,3}|{2}`. Conversely no one-cut split of original `B_S=((3,5),(4,6))` produces `{3,4}|{5,6}`. That false extension is already excluded by CASE 50. Exact rational tests checked query masses for p=2,…,6 and the all-p base/ratio bounds; a zero-loss two-query control exceeded the bound.

Evidence: `referee_case_checks_v1_controls.json` and `referee_case_checks_v1_case.json`, containing inputs, exact spans/clusters, partitions, cuts, hashes and timing. Script SHA-256 is `27ec599f2a1e78197887120f31710cb440e4482f2e22c71db3d85ad367508ef1`; X0 SHA-256 is `16b2a036b1f0ad537789a9e42a69eb9bccce5869b26c90ff6f4f8fc624db500c`. Both evaluations share X0's span/cluster implementation. These fresh hostile tests provide finite evidence, without an independent implementation certificate. No prior X0 receipts, Lean replay or full workspace validation suite were used.

## Proof repairs

**Read.** CASE 20 assumes “every shared vertex has exactly two realized regions for both parents”; CASE 22 concludes “Thus any edge of H induces a mutually clear binary boundary.” CASE 48 says “Its agreement with its target restriction supplies one actual source cut for this split.” CASE 36 requires an actual one-cut A output; CASE 38 permits lower bound two only after every one-cut trial fails.

**Reviewer inference, selector.** For convex leaf spans of disjoint labels, shared vertices are nonlabels. The two occupied regions give degree two in each span. Their connected intersection is a path; a singleton is impossible because two two-element direction sets in ambient degree at most three intersect. At either endpoint the two exterior directions differ. No internal shared vertex has an exterior occupied branch, so the endpoint-sector argument gives clearance. Split formalization into shared-nonlabel, region/degree, convex-intersection, nontrivial-path and endpoint-sector lemmas, retaining nonempty overlap explicitly. No combinatorial flaw was found under those hypotheses.

**Reviewer inference, exchange.** Orient the target edge `e=(u,v)` and put `D=desc_T(v)`. For crossing final block Q, `Q∩D` is a nonempty proper descendant cluster of its target restriction. Rooted agreement transfers that cluster to source Q, giving one restricted source cut. Lift it to an uncut edge along the corresponding source path inside Q's current component. Two crossing B blocks would both contain e; whole A also contains e, forcing at least two A blocks. Splitting Q and merging A therefore does not increase components. This is a proof plan for the expressly open surgery, with no assumption that all original B agrees.

**Reviewer inference, completion/accounting.** The stated actual A cut, whole colors and their homeomorphism give a one-cut local solution; bad A excludes optimum zero. B refinements retain clearance by span containment, and the specific A cut lies in its distinct source namespace. For the other branch let q be the budget after its paid core. Resolve zero/one-cut parents exactly and charge their exact costs. With one unresolved parent, another bad parent removes at least one unit. With p≥2 unresolved parents, every query has budget at most `q−2(p−1)`. The normalized sum is `p/c^(2(p−1))`; at `c=233/100≥2`, its p=2 value is `2/c²≤1/c`, and successive ratios are at most `3/(2c²)<1`. Reject if lower bounds exceed q. A correct exact-decomposition procedure must compute exact local costs; several yes-answers under separately overallocated budgets do not establish a feasible sum. CASE 64 leaves that interface open.

**Bug report:** no confirmed in-scope bug. The rejected whole-B one-cut statement is a false control, not a counterexample to CASE 48–50. Source-core grammar/coverage, global state admission and asymptotic runtime were not tested.

## Abstract-only check

CASE's opening labels the universal arguments proposed and declines a new runtime. RESULT's first substantive line labels the result conditional and the complete algorithm/exponent OPEN, before its active reduction description. No hidden closure claim was found; the small wording repair in the table would improve standalone RESULT phrasing. A facts/numbers pass checked the retained receipts, and a second prose pass checked quotations, locators and scope. CASE and RESULT received no edits.
