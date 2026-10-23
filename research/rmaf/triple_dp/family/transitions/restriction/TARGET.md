# Live child restriction and transition recovery

Status: pinned target, not a proved result. Regime 1. This is the next
increment after the actual merge constructor. No restriction proof has been
written or evaluated at this pin. Completed earlier sources and receipts
remain immutable.

Let `A : CostRoute.Family (.node l r) I`. For `side : Bool`, write `t_side`
for the corresponding child and

```
Live A side i := exists a x, LeafAt t_side a x and A.support i (side :: a).
OpenBranchLive A := forall o, A.boundary = some o -> forall side,
  (exists a, A.support o (side :: a)) -> Live A side o.
```

The premise is required only for the parent boundary index. Prove that all
occupied child restrictions are live: a closed convex region cannot cross
the parent root, and every parent index already contains a leaf. Then
construct an actual child `Family t_side {i // Live A side i}`. Its support
at `i` must be exactly `fun a => A.support i.val (side :: a)`, and its finite
enumeration must select precisely those live parent indices. Its boundary
must be precisely the parent index, if any, containing the child root.
That index may be closed in the parent. Prove every family field rather
than assuming child validity. Preserve distinct indices even when leaf
labels or colors coincide. Unused internal vertices remain unused.

Prove that every parent index is live in one or both children and that an
index live in both is exactly a parent boundary index live in both. Prove
the exact block-count equation

```
childLeft.blockCount + childRight.blockCount =
  A.blockCount + (if the parent boundary is live in both then 1 else 0).
```

Classify `A` by its boundary: none, left only, right only, both. There is no
fifth case with a leafless parent boundary, because `Family.labelled`
excludes it. In the four cases recover, up to an explicit bijection on
indices preserving exact supports, respectively `closeBoth`, `extendLeft`,
`extendRight`, and `merge` of the actual restricted children. The costs are
respectively `cL+cR+bL+bR`, `cL+cR+bR`, `cL+cR+bL`, and `cL+cR`, where `bL`
and `bR` are the child boundary charges. Prove the exact equations on the
actual constructed restrictions, including the closing of a parent-closed
index that owns a child root. An existence statement with no support
equations does not satisfy the recovery target.

Connect the premise to the *concrete* `toClosedAssembly` and
`toOpenAssembly` functions applied to `normalize F`, using
`normalized_open_child_occupied` and their definitional support equations.
`normalized_assembly_exists` alone does not export support equality and
must not be used as if it did.

MAY ASSUME: the actual definitions and checked lemmas in TripleDP,
ConnectedRegions, FamilyModel, FamilyTrim, FamilyGeometry, FamilyTransport,
FamilyAssembly, and the new finite selection/merge modules, with their
printed hypotheses. Shared semantics and source pins must be recorded.
MUST NOT ASSUME: restriction validity, index correspondence, count/cost
equations, branch liveness of an arbitrary raw open support, a cover lemma,
DP legality, graph-hull correspondence, or executable refinement.

Licensed partial delivery: universal restriction constructor and premise
transport, or universal count/cost lemmas, may be reported separately with
remaining recovery obligations OPEN. If the normal form fails, retain the
exact in-regime counterexample, check whether the pin mistranscribed its
hypotheses, and issue a versioned erratum; do not silently strengthen it.

T1 is two leaf children with separate closed parent singleton regions:
parent count 2 and cost 2; each child count 1 and cost 0, with its own
boundary; close-both toll 2. Any mismatch kills the proposed statement or
instrument. The frozen control battery also includes all four transition
types, an unused child root, a parent-closed region owning a child root,
equal leaf values, a raw leafless incursion outside the premise, malformed
families, wrong counts/tolls, and support/index corruptions. X0 must execute
before any proving run, and fresh verification must precede acceptance.

This target is only the family geometry/cost interface. Full G2, color/mask
legality, executable graph correspondence, table/backpointer refinement,
unrestricted algorithms and any improved exponential bound remain separate.
