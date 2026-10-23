# Geometric local-history repair route

Status: setup; no universal runtime theorem claimed.

Scope: source-preserving geometry in literal Chapter 6 G4.1 with P={a}, Q empty and s=3, including local uncles with three/four active roots and reachable three-credit states.

Evidence and claims will be recorded here. Bounded controls are not proofs. Credits and protected edges are distinct. Unary-rho convention remains to be stated from the source.

2026-10-14 pilot notes: v1 control failure was normalization scheduling: a requested nontrivial witness pair was checked before removal of an earlier root-trivial pair. v2 fixed controls but its boundary initially waited until a disappeared, allowing external work; this invalidated the v2 mass target (not a source counterexample). Both failed scripts/logs retained. v3 boundary ends as soon as the local F1 region has collapsed. 100 random inputs completed in 0.04852s, 5 qualifying three/four-root states; projection for 20000 inputs is 9.7s under fixed-size linear scaling. Run 20000 bounded inputs next; no asymptotic inference.

Forest coverage amendment: the first 20000 inputs had connected initial F2. Review exposed the need to include u,v in a separate component from x. This is not a runtime counterexample; the two-protected x,u pair is then disconnected and has zero legal children. The proof now states that alternative. A 100-input forest pilot took 0.05044s; the same fixed-size linear projection gives about 10.1s for 20000 forest inputs. The forest generator makes one internal cut before setting protections; generated states remain locally admissible test states, not claimed full-history reachable.

## Current deliverable

`PROOF.md` contains a conditional geometric argument for the C-child allowance with three/four active roots. It explicitly handles three protected active endpoints and proposes an empty-credit frontier annotation. Its ordinary tree arguments await independent review. `Geometry.lean` proves the conditional surviving-descendant kernel and exact arithmetic; it does not formalize the source algorithm.

The checker is a one-shot instrument for this source-rule repair. Use it to challenge local states, exact branches, protected sibling survival, and discounted mass at the point the local F1 region disappears. The output is bounded computational evidence: generated states satisfying local assumptions may be unreachable from an unprotected root. A no-fire result cannot be used as an asymptotic theorem. Trust an executed check only with its controls, exact denominator, source hash, and the stated covered starting-state distribution.

Replay from the workspace root:

```
./bootloops-python research/rmaf/thesis_complexity/repair/geometry/check-v5.py --count 20000 --out /tmp/geometry-connected.json
./bootloops-python research/rmaf/thesis_complexity/repair/geometry/check.py --forest --count 20000 --out /tmp/geometry-forest.json
./bootloops-python research/rmaf/thesis_complexity/repair/geometry/disconnected_control.py
./bootloops-lean research/rmaf/thesis_complexity/repair/geometry/Geometry.lean
./bootloops-lean research/rmaf/thesis_complexity/repair/geometry/FalseGeometry.lean
./bootloops-python research/rmaf/thesis_complexity/repair/geometry/package.py
```

The FalseGeometry command must fail. The positive Lean file must pass. The package checks both exit codes and the saved run hashes. No custom Lean axioms, sorry, or native_decide occur in the accepted file. The Mathlib import failure is retained; the accepted formalization uses Std only. All seven reported controls ran. No aggregate theorem count was edited.

Measured final evidence: connected run 20000 inputs / 875 qualifying local states; forest run 20000 inputs / 346 qualifying local states. Maximum exit mass 1/4 in both three-root and four-root classes. Across the runs, 2626 descendant source cut sets preserve the protected sibling, 312 tested ABC children avoid a free merger, 104 connected two-protected pairs have at least two pendants, and 158 visited states carry three active protected roots. An additional explicit disconnected pair control has zero legal branches. Those last counts describe protection; only the frozen thirteen-leaf witness claims the literal P={a,x,u},Q={x,u} annotation.
