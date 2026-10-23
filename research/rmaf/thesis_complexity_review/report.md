# Independent review of the Chapter 6 runtime audit

The two reported defects in the local proof steps reproduce. A legal nine-leaf trace reaches the exceptional G4.1 substitution with coefficient 9/16 against 1/2; a legal thirteen-leaf trace reaches three analysis credits despite the stated limit of two. Both statements concern the complete tree of permitted recursive calls. Neither establishes a runtime lower bound or refutes O(2^q n). The nine-leaf C-child terminates without further calls.

I reconstructed the source rules before reading the producer's report or Lean files, wrote a new graph implementation without importing producer code, and compared its results with the supplied certificates. I also replayed all 28 stated Lean axiom audits in an isolated directory. A proposed local repair covers G4.1 with two active leaves, but the three- and four-leaf cases remain open.

## Source reconstruction

The source is the retained Whidden thesis PDF with SHA256 `0dd9ced63f26ab608dc484cfe853d52171565b0cc704bb61336dd64a15c2bbe9`. Printed page p corresponds to PDF page p+13. I read Chapter 6 algorithm and proof text, including printed pp116–126; images supplied the omitted text on pp110 and 118 and confirmed the formulas on pp117 and 123. Chapter2 p12 confirms the labelled unary rho root convention used by both finite trees. No conversion to the unaugmented convention is claimed here.

The exact source-to-model reconstruction and preregistered controls are in [source-freeze.md](source-freeze.md). On p117, the source restricts P to at most two nodes, requires Q⊆P, and assigns

`B(K,p,r)=α·2^K·(2+r)/2^(p+1)+p−3`,

where K is remaining cuts, p=|P| and r=|Q|. The source writes k for K and q for the pendant count. Its recurrence counts the current invocation, as indicated by the initial 1 in the inequalities on pp117–118. The induction on K assumes only the smaller-budget empty-credit bound; nonempty-credit states are handled through G1–G6. Thus an arbitrary inequality between credit counts does not supply the missing structural proof.

The relevant algorithm requirements are the ordered cases in Figure6.5 p111, depth selection on pp110–111, and protection/cut/suppression rules on p107. The supplied trees satisfy these requirements. The deeper-first orientation is explicit in the proof's use on p121 (“contradicting how we order the members”); the displayed depth rule principally describes the selection of an unordered sibling pair. The reviewed examples obey the stronger orientation convention used in the proof.

## Nine-leaf trace

The independent checker retains detached F2 components until Steps5/6 select and remove their matching active F1 roots. It recomputes the deepest protected top endpoint, eligible cherries, F1 depths, component separation, and F2 depth tie-breaks from graph adjacency. Its earlier-case predicates compare unordered rooted topology, rather than relying on child order in a printed tree.

| Invocation | Chosen pair | First case | Pendant nodes | Analysis P,Q | Chosen child |
|---|---|---|---|---|---|
| G1 | a,c | A2BC | {d,t,w,x,y,z}, h | ∅,∅ | C: cut c |
| G3 | d,a | A2BC with protected a | {t,w,y}, {x,z} | {a},∅ | A: cut d |
| G4.1 | y,x | A3BC | w,t,z | {a},∅ | C: cut x |
| G5 | y,a | A3BC | w,t,z | {a,y},{y} | none legal |

All earlier cases fail at the G4.1 invocation, and all three candidate branches there are legal. The original P={a},Q=∅ is preserved by the source's G3 A2BC endpoint-cut assignment (p120). In G4.1 the exceptional p123 assignment gives the A-child the original credits, resets the B-child, and adds y to both credit sets in C. Therefore

`(1/2)(1/2)+(1/8)(1)+(1/2)(3/8)=9/16 > 1/2`.

With X=α2^K/16, the complete substituted child allowance is 9X−5 and the parent allowance is 8X−2. At X=4 these are 31 and 30; this is an illustrative scaling, not a choice of the source's base-case constant. The failure persists whenever α2^K>48, and hence for arbitrarily large K with any fixed α>0. The independent calculation also checks α=128,K=0, which gives child allowance67 against parent allowance62 and accommodates the source's displayed representative base cases. These comparisons concern allowances. The independently replayed C-child has protected endpoints a,y and protected pendant z, so it makes no recursive call; its actual descendant count is 1. The source's stated individual child bounds therefore do not justify the local substitution, even though a tighter estimate can cover this example.

The replay starts with cut budget10 to keep every displayed state above the negative-budget test. It follows the full permitted-call tree. It does not assert that an implementation which stops on an earlier successful child visits this path. The complete tree remains a legitimate upper-bound object; the observed local proof omission alone cannot establish a failure of the short-circuit implementation's runtime.

## Thirteen-leaf trace

The independent replay agrees with all five states of the supplied thirteen-leaf certificate, including their protected-edge sets and candidate branch legality. The successive chosen pairs and analysis assignments are:

| Pair | Case | Pendant count | P,Q before branching | Selected branch |
|---|---|---:|---|---|
| a,c | A2BC | 2 | ∅,∅ | C |
| d,a | A2BC | 2 | {a},∅ | A |
| x,y | A3BC | 4 | {a},∅ | C |
| u,v | A3BC | 4 | {a,x},{x} | C |
| u,x | A2BC | 2 | {a,x,u},{x,u} | endpoint cut forbidden; B legal |

G4.1 adds x. At G4.2 the source's general union instruction on p123 applies to the G2 A3BC assignment, adding u while retaining a and x. Thus |P|=3 is a reachable assignment under those literal instructions. This is a defect in the stated domain of that proof. Extending the domain may repair it; a larger P does not by itself increase the exponential base. The p119 prose's Q∪{v} conflicts with its displayed Q∪{u}; this review follows the displayed recurrence and records the prose discrepancy separately.

## Arithmetic and Lean

The fresh Fraction calculation reproduces all 44 supplied diagnostic transition rows, including coefficient sums, additive offsets and state-domain indicators. Source-forbidden abstract rows remain diagnostics and are not promoted to reachable defects. Eight supplied trace states agree exactly in pair, case, pendant list, protected-edge sets and every candidate branch; the fresh replay additionally follows the nine-leaf C-child.

Both producer Lean modules import only Std. I copied them without changes into `lean-clean`, set LEAN_PATH empty, and ran the repository's pinned `./bootloops-lean`. Their 28 printed axiom audits contain only propext, Classical.choice and Quot.sound; several are axiom-free. A source scan found no custom axiom declarations, sorry, admit or native_decide. The negative-control log contains Lean's explicit diagnostic that `9 ≤ 8` is false. The corresponding true proposition and an affine true twin compile and print no axioms.

The scope of the formal statements is narrower than a formal runtime theorem:

| Formal material | What it establishes | What remains outside it |
|---|---|---|
| Credit.lean | Affine identities/inequalities for X:Int and credit counts:Nat | Structural reachability, descendant estimates, and a general real-α formalization |
| Trace.lean | Finite evaluations of the supplied tree/cut/predicate expressions | A universal semantics for every algorithm invocation |
| RepairArithmetic.lean | The proposed strengthened C estimate algebraically implies the local joint estimate | The geometric hypothesis for all G4 states |

In particular, Trace.lean receives its depth-domain top subtree as an argument; its finite theorems do not implement a universal derivation of that top. The fresh graph checker computes the top from every protected F1 edge. The producer's root-sibling exclusion theorem covers the nine-leaf data; the fresh checker also evaluates that rule on every candidate cut in the thirteen-leaf trace. These additional checks support the finite correspondence without expanding the formal theorem's scope.

## Repair and remaining work

[local-repair.md](local-repair.md) gives a proposed geometric proof for G4.1 with exactly two active leaves x,y in the local uncle subtree. The original A2BC history leaves a protected edge to a's sibling subtree b. If x lies outside b, the C-child is blocked by b. If x lies inside b, legality of J's B-child forces y inside b too. Three pendants and the deeper-first orientation imply that, after cutting y, the a–x path has at least three pendants. Thus C has at most one legal child, cutting at least two edges, which suffices for the stronger bound `I(C)≤α2^(K−3)−1` under the stated empty-credit induction bound and a suitable base constant.

The argument is newly authored in this review and needs a separate proof review before a verified status. Its exact diagnostic examples include a live C-child with three pendant cuts and a planted omitted-orientation case with only one pendant; the checker rejects the incorrect orientation. Those post hoc examples illustrate the hypothesis and do not constitute a proof by enumeration.

With three or four active leaves, C first processes additional sibling pairs. The remaining obligation is a joint descendant estimate retaining the protected-sibling history and covering the demonstrated three-credit state. A timing census cannot replace that estimate. The O(n) local-work implementation claim on p116, the complete algorithm's correctness, and the transfer from the labelled-rho convention were not established by this review.

## Reproduction and limits

Run, from the workspace root:

```sh
./bootloops-python research/rmaf/thesis_complexity_review/replay.py --controls
./bootloops-python research/rmaf/thesis_complexity_review/replay.py --witnesses
./bootloops-python research/rmaf/thesis_complexity_review/audit_receipts.py
./bootloops-python research/rmaf/thesis_complexity_review/repair_controls.py
```

Fourteen pre-witness controls passed, including planted wrong topology, illegal cut, wrong depth choice and wrong budget checks with positive twins. The final two-witness replay took 0.012953083 seconds inside the process. Clean Lean pilot/replay times were 0.35 and 0.52 seconds, recorded only as operational measurements. Source hashes, exact trace records, row comparisons and axiom lists are retained in `../results/thesis-complexity-review-*.json` and the corresponding logs.

The producer's Python runtime was not opened or imported; its JSON certificates were used as the objects being checked. Source PDF, candidate trees, source mathematics, Python Fraction and the Lean kernel are shared inputs or infrastructure. The assignment disclosed the alleged headline values before this review began, so this is an independent reconstruction and adversarial check, not a blind discovery. No thesis-correctness or transfer files were read. No upstream toolkit files were changed, no hosting was used, and the general BootLoops validation suite was not run by this review.
