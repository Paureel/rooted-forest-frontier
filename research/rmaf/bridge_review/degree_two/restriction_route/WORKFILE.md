# Restricted-tree transport route

Owner: /root/astra_bridge_review/degree_two_restriction_route
Status: skeleton; controls and immutable route pin pending.
Scope: cross-tree transport of actual support disjointness for a nonempty two-block partition of a common selected label set whose restrictions agree. Restriction associativity and isomorphism preservation are prerequisites. No claim about the one-tree split construction, partition replacement, G3/G4, clearRest, runtime, or novelty.
Isolation: do not read graph-adversary code, derivation, or parent LocalSplit before completing own controls and immutable route pin. No children.
Evidence: exact positive/false controls, diagnostic controls, timings, source hashes, axiom receipts, and Lean build receipts retained here.

## Completed derivation and evidence

The immutable pin was sent to the parent before general proof construction:
SHA256 `3d509aed2ba81aa77b96525a2fb92252a8acbb676042d774d345847b8d1988d5`.
The promised graph X0 no-fire was supplied by the parent; its checker and output
were not opened here. The route remained isolated through delivery.

`ROUTE-AMENDMENT-v2.md` records the direct support-summary alternative to the
planned clade interface. This removes the need for a clade-equivalence lemma;
`supportProfile_restrict` explicitly proves suppression invariance instead.
All final theorem statements refer to the original executable definitions.
No exact transport obligation remains open in this route.

The first complete clean replay printed, verbatim:

```
{"receipt": "/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/bridge_review/degree_two/restriction_route/replay/20261014T145454Z/receipt.json", "status": "all requested author checks passed"}
```

Its main axiom receipt, verbatim:

```
'RestrictionRoute.two_block_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'RestrictionRoute.supportProfile_restrict' depends on axioms: [propext, Quot.sound]
'RestrictionRoute.supportProfile_rootedIso' depends on axioms: [propext, Quot.sound]
'RestrictionRoute.actual_disjoint_transport_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RestrictionRoute.actual_disjoint_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The strengthened replay also binds negative-control source hashes and compiled
object hashes, enforces the printed axiom allowlist, and checks source hashes
again after execution. See FINAL-REPLAY.json for its exact receipt.

## Timing and provenance

The source-build pilot measured RMAF at 6.009979667 seconds and the positive
control file at 0.403586792 seconds. The first final replay measured the source
modules individually; SupportProfile took 0.726425125 seconds and
ActualSupportTransport took 0.381730000 seconds. These are observed local times,
not algorithmic complexity claims or forecasts. No larger census was launched.

No leastness module was needed. The only external mathematical production
source was RMAF.lean, SHA256
`4960d5be9a5f1eb6b15d11c76130bee5263125631314a4eb2d43d500d5b513a9`,
plus Lean Std. Final module/log hashes are in the replay receipt.
Controls were frozen before execution; later compile errors influenced proof
editing and are author-side diagnostics, not independent reference values.

## Reading ledger

Read and retrieved from the pinned RMAF.lean bytes:

- Line 28, `inductive RootedIso : Tree → Tree → Prop where`: constructors include
  straight and swapped node isomorphisms. This is a retrieved definition.
- Line 48, `theorem sameShape_correct (t u : Tree) : sameShape t u = true ↔ RootedIso t u := by`:
  the Boolean/inductive equivalence is retrieved and used at the transport seam.
- Line 84, `def restrict (selected : List Nat) : Tree → Option Tree`: node cases
  suppress one surviving child and keep a node when both survive. Retrieved.
- Line 116, `def rootedSpan (selected : List Nat) : Tree → List Vertex`: contributes
  this root whenever either child has selected descendants. Retrieved.
- Line 126, `def minimalVertices (selected : List Nat) : Tree → List Vertex`: skips
  roots until two children contribute, then includes both rooted spans. Retrieved.
- Line 135, `def disjointVertices (a b : List Vertex) : Bool :=`: checks every
  member of a is absent from b. Retrieved.
- Line 144, `def restrictionAgrees (t u : Tree) (b : List Nat) : Bool :=`:
  compares the two successful restrictions with sameShape. Retrieved.

Derived here, not attributed to the source: restriction associativity,
hereditary agreement, support-summary composition, suppression invariance and
cross-tree transport. There is no external literature or novelty assertion.

## Remaining acceptance boundary

Author grade is CLOSED-UNVERIFIED for local transport. A nonauthor must rebuild
from the pin, reconstruct the fixture values independently, and trace the
parent's original agreement-partition consumer. This route does not claim the
one-tree cut, nested-support/mark consequences, partition replacement, G3/G4,
clearRest or the whole degree-two theorem. The full toolkit battery was not run;
only the required problem-specific Lean replay and frozen controls are claimed.
