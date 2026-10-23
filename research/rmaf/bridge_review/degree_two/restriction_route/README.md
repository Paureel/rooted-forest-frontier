# Restriction and actual-support transport

This route proves universal Lean lemmas for the actual `RMAF.Tree`, `restrict`,
`rootedSpan`, `minimalVertices`, `restrictionAgrees` and `disjointVertices`.
Use it when two trees agree on a common selection and a consumer needs agreement
or support-disjointness for selected subblocks. It does not construct the
source-tree degree-two split or replace a block in an agreement partition.

The final entry points are in `ActualSupportTransport.lean`:

- `actual_disjoint_transport_eq`, line 85: A⊆B and C⊆B plus agreement on B imply
  equality of the actual disjointness Booleans in t and u.
- `actual_disjoint_transport`, line 104: the directed true-valued corollary.
- `two_block_transport`, line 114: with nonempty A,C and B⊆leaves(t), returns
  both block agreements and target-tree support-disjointness from source-tree
  support-disjointness.

`RestrictionTransport.lean` independently derives restriction composition,
its subset specialization, restriction preservation of RootedIso, and hereditary
restriction agreement. `SupportAlgebra.lean` proves elementary support-list
intersection rules. `SupportProfile.lean` proves exact node composition for a
five-field summary of span emptiness and span/minimal-support disjointness.
`ActualSupportTransport.lean` proves this summary invariant under pruning,
unary suppression, and rooted isomorphism. These are proven properties of the
executable definitions; none is an assumption in the final transport theorem.

Run from the workspace root:

```
./bootloops-python research/rmaf/bridge_review/degree_two/restriction_route/replay.py
```

Each replay makes a fresh build directory, rebuilds RMAF and every route module,
compiles the frozen positive controls and concrete consumer examples, demands
explicit falsity from seven negative twins, and keeps malformed diagnostics
separate. It verifies allowed printed axioms, rejects forbidden proof escapes,
and binds every source, log and object to SHA256. `FINAL-REPLAY.json` points to
the latest receipt. Failures abort with their output retained; completion text
is emitted only after every required check succeeds.

Control truth is hand-constructed in `CONTROL-PIN.md`. The first comparator
expected a different Lean falsity string and failed closed; the correction and
all attempts remain. `*-attempt*.lean` and their logs are historical failed
elaboration diagnostics and are not proof evidence. They are excluded from
final builds. `ROUTE-PIN-v1.md` is immutable; `ROUTE-AMENDMENT-v2.md` records the
derived switch from a clade detour to direct support-summary recursion.

No graph-route, parent LocalSplit, or other transport implementation was read.
Only the frozen target, actual RMAF source, toolkit guide and skills were shared.
The author's controls/replays are not independent certification. Grade:
CLOSED-UNVERIFIED for this local transport route, awaiting a nonauthor fresh
review and the parent's use-site trace. The full degree-two refinement and
G3/G4 remain outside this route's certification.

2026-10-14: first implementation. This is purpose-specific proof/audit code;
no toolkit package or upstream frozen source was modified. No larger search,
full toolkit battery, runtime bound or novelty claim is reported.
