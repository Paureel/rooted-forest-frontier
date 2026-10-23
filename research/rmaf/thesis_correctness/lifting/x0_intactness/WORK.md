# X0 minimum-intactness adversary workfile

Status: open; target read before any other route material.

## Assigned claims

- S_every: every globally minimum actual current-F2 AF cutset avoids strictly internal edges of an identical full proper pendant subtree.
- S_exists: existence of an intact global minimum, tracked separately.
- S_contract: exact contraction interface and cost hypotheses.
- Rejection twin: arbitrary-child residual optimality need not imply global optimality.

## Independent implementation

Fresh standard-library exact rooted agreement-forest evaluator; no prior candidate, repair proof, or evaluator imports.

## Controls

Pending: read frozen controls and execute minimum_controls before search. Stop on any mismatch; retain exact witness and do not repair pins silently.

## Source conventions

Pending: inspect retained thesis printed pp. 12, 15–18, 107.

## Domains and denominators

Whole trees and compatible cut/yield current forest pairs; distinguish all minimum cutsets, common subtrees, every-optimum violations, existence failures, arbitrary AF cutsets, forced-extension minima, and inclusion-minimal cutsets. Unary labelled rho, absent/unlabelled component roots, discarded empty fragments, and contraction comparisons require explicit counts.

## Executed results

None yet. No universal inference is licensed by finite testing.

## Method and provenance pin, 2026-10-14

This is an X0 falsification run only. The toolkit index contains no rooted agreement-forest cutset enumerator; the listed graph tools target Feynman-integral graph geometry and do not cover rooted label-preserving forest deletion. A fresh one-shot evaluator is necessary for the explicitly required independent lineage. It will import only the Python standard library, the frozen target/control files, and the retained thesis source. Existing candidate and repair evaluators/proofs are excluded. The deepest shared layer with other routes is the target's forest/AF definition and its frozen controls; this run does not provide a fresh nonauthor verification of its own code.

Controls are exact equality checks. Any failed expected value halts before search and retains actual data. Additional comparator mutations will demonstrate detection rather than silently changing a control. The finite search denominators will never be promoted to universal proof.

## Source reading receipt

Opened `research/rmaf/sources/baseline/whidden-thesis-2013.txt` in this session. The file uses explicit `=== PDF PAGE N ===` markers, not form feeds; an initial form-feed lookup failed before any extraction and is excluded. Printed p.12 = PDF p.25, p.15 = PDF p.28, pp.16–18 = PDF pp.29–31, p.107 = PDF p.120.

Read facts (local text extraction; ligatures/OCR notation retained in source):

- Printed p.12, lines 821–829: the augmented root has a distinct label and its only child is the original root; the source says “we consider ρ to be part of X.” Suppression deletes an unlabelled node and reconnects its parent and child when both exist. This supports retaining labelled unary rho and suppressing unlabelled unary roots without inventing a parent.
- Printed p.15, lines 932–944: an empty component induces the empty tree; AF means a forest of both inputs. The source defines the objective as “the size of the smallest edge set E” whose yielded result is an AF. Actual current-F2 edge counts, not assumed component-count identities, are the audited objective.
- Printed p.16, lines 986–991: subtree notation is induced by all descendants including its root, and existence in the other forest requires equality of those subtrees. An equal label cluster without equal rooted topology is insufficient.
- Printed pp.16–17, Lemma 2.1, lines 996–1020: shifting concerns an unlabelled empty component and preserves the yielded forest. I do not assume it in the evaluator.
- Printed p.17, Lemma 2.2, lines 1021–1035: the current-state compatibility premise groups F2 components into the matching label blocks of F1. An enumerated compatible structural pair is not thereby a reached algorithm state.
- Printed p.18, Lemma 2.4, lines 1048–1054: being a forest also requires absence of component overlaps and incompatible triples. The evaluator will instead enumerate all cut/yield outputs of F1, avoiding use of this characterization as an unproved computational shortcut.
- Printed p.107, lines 5863–5866: “If at least one of e1 and e2 is protected in F2, then e inherits this protection in F2 ˜ Ei.” This is the source's rule, not an assertion that every child is globally optimal.

No background theorem or prior minimum-intactness/repair route was read or imported. The run's convention choice is the TARGET's explicit labelled-root forest model, checked against these passages.

## Initial control pilot

The first invocation passed `identical-common-cherry` and then stopped on an implementation assertion while rebuilding the contracted graph: `from_signature.add` did not return its allocated vertex ID. This is an evaluator construction bug, not a comparison mismatch or an adjusted frozen value. No search ran. The returned ID is corrected below; the original first-control receipt is preserved as `thesis-correctness-lifting-x0-intactness-controls-v1-initial-partial.json` before a full rerun.

## Executed controls and first search pilot

Full rerun of six frozen minimum controls passed. The comparator uses exact typed equality and each compared expected value was also tested against a deliberately wrong tagged object; all such comparator corruptions were caught. Controls are construction fixtures, not an independent certification of this evaluator.

Pilot: exhaustive whole trees on 3 and 4 ordinary labels, both with and without unary labelled rho, using identical code and full domain checks. The 4-label domains each contain 225 ordered tree pairs; measured times were 0.0215 s without rho and 0.0464 s with rho. All 156 common-subtree occurrences across the four domains had an intact minimum and no minimum that cuts strictly inside the subtree. Nonminimum inclusion-minimal AF cutsets did violate intactness (36 per 4-label root convention), proving that inclusion-minimality is a different quantifier.

The next pilot samples 200 ordered pairs per 5-label whole-tree domain and 2000 ordered pairs per current-forest domain. Full unknown runtime is not inferred from the 4-label timing alone. Progress units are evaluated structural pairs, common-subtree occurrences, and enumerated minimum cutsets; CPU activity is not a scientific check.

## Scaling decision

The 5-label whole-tree pilot used 200 random ordered pairs per root convention (seed 14102026, deterministic size/convention offsets), including 45 / 58 common-subtree occurrences without / with rho. Timings were 0.1604 / 0.4533 s. Linear same-distribution projection to 11,025 pairs per convention is 8.84 / 24.99 s; cold cache costs are included, so this is a conservative practical launch estimate rather than a formal runtime bound. Full enumeration is well below the timing threshold.

The current-forest pilot enumerated all cut/yield forests from all labelled binary source trees through 4 labels. It found 37 distinct current forests without rho and 104 with rho at n=4. Whole current-pair spaces are 1,369 / 10,816; sampled/full observed times project below one second. The current n=5 domain will be piloted separately before extension.
