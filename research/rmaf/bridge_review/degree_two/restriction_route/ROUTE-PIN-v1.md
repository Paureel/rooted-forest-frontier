# Immutable restriction/isomorphism route pin v1

2026-10-14. Written after positive controls and seven explicit falsity catches;
before general proof construction and before cross-reading. Separate graph
adversary's no-fire verdict supplied by parent; its evidence/code not read here.

## Exact intended target

For actual RMAF trees t,u, duplicate-free leaves in each tree, nonempty
B, B.Nodup, B contained in leaves t and leaves u, and
restrictionAgrees t u B=true: if nonempty A,C are a duplicate-free disjoint
partition of B (membership x∈B iff x∈A or x∈C), and actual
minimalVertices A t and minimalVertices C t are disjoint, then actual
minimalVertices A u and minimalVertices C u are disjoint.
No equality of global leaf sets and no equality of cross-tree addresses.

## Route and prerequisites

1. Establish restriction composition by structural induction on actual Tree:
restrict A after restrict B equals restricting by membership intersection.
Derive the subset specialization for A⊆B.
2. Establish preservation of RootedIso under restriction using the straight and
swapped constructors, including empty and singly surviving children.
3. Derive hereditary restrictionAgrees for nonempty subsets occurring in t.
4. Establish the remaining combinatorial support interface: two complementary
nonempty blocks of B have disjoint actual minimal embeddings exactly when one
block is a proper selected clade in the suppressed restriction to B. This
requires a proof connecting actual unsuppressed supports to the restricted tree;
there is no assumed address identity and no assumed support transport.
5. Transport the clade property via rooted isomorphism, then use the interface
backwards in u. If this cannot be completed, deliver compiled prerequisites and
an exact typed missing support lemma whose conclusion is explicit.

## Frozen checks and lineage

CONTROL-PIN.md fixes all literals. Controls.lean passed; seven false propositions
were rejected by `decide` with `is false`; malformed identifier rejected only as
a diagnostic. controls-receipt.json retains measured timings and source hashes.
The first comparator expected a different Lean error string and failed closed;
controls-receipt-attempt1.json and run_controls-attempt1.py preserve that event.
Its predicate was corrected to match Lean's explicit falsity wording without
changing any proposition or pass/fail expectation.

No graph-route code, derivation, or parent LocalSplit has been read. The only
shared mathematical production source is actual RMAF.lean. This route's checks
are self-authored and cannot replace a nonauthor fresh review.

## License

Full transport or partial compiled prerequisites plus explicitly typed missing
lemma. No custom axiom, sorry, admit, native_decide, generic transport predicate
hiding the conclusion, G3/G4/clearRest closure, runtime bound, or novelty claim.
