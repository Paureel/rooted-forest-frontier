# Source ledger

Retained source: research/rmaf/sources/baseline/split-or-decompose-v2.txt.
The final manifest records its exact hash. PDF page markers in that file fix
these locators; the source was opened in this author session.

| Read source | Actual claim used |
|---|---|
| PDF p3, Preliminaries | T[A] is the minimal original subtree connecting A; rooted restrictions suppress unary path vertices. |
| PDF p4, Rooted trees / Agreement forests | Proper rooted binary syntax; equality of rooted restrictions and vertex-disjoint original embeddings in both trees. |
| PDF p4, footnote2 | The source omits the extra root taxon rho. |
| PDF pp6–7, Whidden | Outgoing child arcs have tails on the a–b path and heads outside it; t=1 is a deterministic special case. |
| PDF pp17–18, Rule4 / Lemma12 | Actual source cherry ac and target cherry ab, two source pendant groups, branches cutting both groups / a / ALL swapped a–c outgoing arcs, and the informal no-larger exchange case. |

The disputed source passage (PDF p18), copied from the retained bytes:

```
IfB contains taxa fromX2, but notc, we can cut offX2 and
add b (which will necessarily be a singleton) toB, irrespective of whetherB contains taxa
from outside{a,b,c}∪X2: again, we are back in the first branch.
```

The original mathematical exchange proof here is a derivation from the source
model. It proves target topology by an agreed final-block cluster and a leaf
graft, and proves global source separation through the retained source
restriction and the original X2 clade. The retained source does not contain
these Lean arguments. Their correctness requires the exact code/proof review,
not attribution to the informal paragraph.

Completed development inputs: frozen hard-refinement 20261015T084225Z;
output-state 20261015T105826Z; final-cuts replay 20261015T105812Z. The final
SOURCE-INPUTS-v1.json and replay receipt record each exact source module. All
these contacts are on the author production side of the independence ledger.
The existing Python oracle was also a development contact; its matching finite
answers cannot certify this Rule4 implementation independently.

The root producer-audit amendment was read at
research/rmaf/algorithm/verification/ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md. The audit
implementation was derived from that requirement and actual Lean 4.35.0
Environment/Declaration/CollectAxioms source. No independent reviewer's audit
implementation was read. New detector controls are separately versioned and
post-contact with the mathematical candidate, as AUDIT-CONTROLS-v1.json states.

No novelty or literature-exhaustiveness claim is made. No bibliography file was
created or edited. Unfinished main both_bad, cherry_branching author, other
unfinished proofs and independent reviewers were not consulted.
