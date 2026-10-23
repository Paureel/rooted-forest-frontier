# Independent component/partition adversary

Status: construction begun; no proof or scientific acceptance claim yet.

## Target and permitted premises

Reconstruct rooted agreement through leaf blocks, induced rooted subtrees, and disjoint minimal embeddings. Test root-safe common-cherry normalization only with explicit validity, component containment, and agreement-forest compatibility; separately expose standalone failures and compound-subtree quantifiers.

## Source ledger

Pending primary definitions (pp. 12–18), Lemma 6.5 (pp. 101–103), and consumers (pp. 112–116).

## Frozen controls

Pending controls.json: universal raw-Cover failure; standalone normalization failure; compatible twin; missing-parent fixture.

## Independent evaluator

Pending construction. No sibling route, original implementation, or reviewer code will be read during construction.

## Pilot and adversarial results

Not executed.

## Proof route

Not authorized until executed adversary result is reported.

## Executed result before proof construction — 2026-10-14

**FIRE: the unrestricted equal-compound-subtree statement fails even under component containment and actual active AF compatibility.** This result is exact finite evidence from this evaluator; fresh nonauthor verification is pending.

Take unary-rho trees

- T1 = (((a,(c1,c2)),b),d), with F1 = T1;
- T2 = ((a,(c1,c2)),(b,d)), with F2 = T2;
- sibling roots a (ordinary leaf) and c = (c1,c2) (compound subtree);
- E = {ea, ec1, ec2}, and E2 = empty.

Both sibling subtrees are identical in F1 and F2. Every F2 component lies in an F1 component. F2~E has blocks {a}, {c1}, {c2}, {rho,b,d}; the last induced tree is rho→(b,d) in both originals, and all four minimal embeddings are disjoint. Thus it is an AF of both original trees and both active forests.

Exactly one E edge lies on path(a,c): ea. The root-safe rule restores ea and retains ec1,ec2. The resulting blocks are {c1}, {c2}, {rho,a,b,d}. The final large block contains bd|a in T2 but ab|d in T1. Hence the result is not an AF. The LCA has a parent, so repairing only the missing-parent case cannot address this witness.

The failing source proof assertion is the p.102 existence of a label x1 in Fa∪Fc that stays connected to u after E: a is detached and both labels below c are detached. The skeleton from c to u carries no such label. The rule does not cut incoming eu when it removes just one path edge.

Scope: this witness satisfies the explicit structural active-state invariants, but it is not claimed to be an algorithm-reachable state after all common-subtree reductions. E has three cuts and is not asserted optimal. A theorem limited to optimal E, to intact contracted atoms, or to an explicit surviving-label condition would be a different statement requiring its own proof and consumer audit.

## Executed controls and root pilot

Script: `evaluator.py`. Frozen input: `../controls.json`. Commands and logs are retained in the result directory. The controls ran first, before the adversary.

Exact control output:

```json
{"compound_in_regime": null, "compound_normalized_AF": null, "controls_passed": 4, "negative_controls_caught": 4, "receipt": "/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/results/thesis-correctness-repair-component-controls.json", "root_boundary_tested": 0, "seconds": 0.0026927920007437933, "stage": "controls"}
```

Exact pilot output:

```json
{"compound_in_regime": true, "compound_normalized_AF": false, "controls_passed": 4, "negative_controls_caught": 4, "receipt": "/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/results/thesis-correctness-repair-component-pilot.json", "root_boundary_tested": 40, "seconds": 0.015185457999905339, "stage": "pilot"}
```

The pilot exercised 40 genuine structural root-boundary premises with absent incoming LCA edge and at least two removed path edges; each had ordinary-leaf endpoints, E2 subset E, genuine original AF, active AF compatibility, and component containment. No failed normalization occurred in these 40 cases. This is not exhaustive and not proof. In all these cases the rho edge had already been cut from F2; F1 remained the source tree. The retained witness rows provide explicit labels and cuts.

Timing: pilot began after the four frozen controls passed. The complete measured pilot took about 0.0152 s internally. No larger run was launched on an unmeasured estimate, and no runtime theorem is claimed.

## Consumer consequences observed from source

- Lemma 6.10, first exchange (a,c): ordinary-leaf endpoints or protected intact atoms would avoid the erasure mechanism, but the printed sibling definition itself permits compound subtrees and the optimum extension E0 can contain more edges than the displayed local E. An adequate theorem must state and establish its precise residual-label/optimality hypotheses.
- Lemma 6.10, second exchange (x,u): u is explicitly the merged subtree on a and c, so an ordinary-leaf-only theorem does not directly apply. Merely calling u an atom requires a proved contraction/lifting statement preserving the relevant cuts and costs.
- Theorem 6.12, final exchange: its E0 is an optimum extension, so the present nonoptimal witness does not by itself refute that consumer. Its compound siblings still require an explicit optimality or intact-subtree lemma; the unrestricted Lemma 6.5 cannot supply it.

No proof constructed. Parent notified of the executed result and pending authorization for a restricted component/partition proof route.
