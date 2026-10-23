# Independent balanced safe-cover target

User-authorized priority, 2026-10-14: independently prove the missing safe-cover lemma in the supplied RESEARCH.md and connect it to a complete faster algorithm. Use GPT-6.1 Sol xhigh. This is main-algorithm work; no standalone thesis repair.

## Exact source target

Source: `sources/previous-work/RESEARCH.md`, Section8, lines230–246. Its preserved SHA256 is `960bff1cb96bf7501e2dc27c23cb5b29303378816d9b7249a5740151706e3865`, identical to the user's Downloads file. The source explicitly calls this a research target, not a proved theorem.

Given a reduced ordinary rooted binary tree pair on the same distinct labels and integer cut budget b, construct in O*((5/4)^b) time at most O*((5/4)^b) source-forest refinements F_j such that:

1. Each F_j uses at most b counted, nonredundant source cuts.
2. If the original optimum is at most b cuts, at least one ORIGINAL optimum refines some F_j. Preserving one optimum suffices; preserving every optimum is not required.
3. Each F_j is in the pure-bridge completion class or the compatible/triple polynomial terminal class described in the note.
4. In every pure-bridge F_j, tau=max_D d_D is at most b/2, where d_D is the original unmarked local cut distance, not a later marked-query budget.

The leaf-partition refinement relation, unsuppressed vertex disjointness, actual source cuts, reduction history and original-label reconstruction must be explicit. No rho is implicitly added. Original component parameter k corresponds to b=k-1 at the successful decision budget.

## Algorithm consumer

Give total pseudocode or code: generate the cover, complete each forest exactly with its paid local queries, add precut and residual costs, reconstruct a valid agreement forest, and return the least cost or a valid budget failure. Iterate decision budgets without using an optimum oracle inside the algorithm. Prove validity, optimum survival, termination and the full charged runtime.

The note's products near1.94 and1.91 are conditional. Do not accept them as new established runtimes. Pure-bridge and triple-terminal correctness, marked role-swap and executable correspondence are separate imports to discharge; existing generic/conditional Lean modules do not discharge their missing fields.

A weaker cover is an explicitly licensed alternative only if its actual generation size/time alpha^b and hardest local fraction theta produce a rigorously proved complete bound with base alpha*c0^theta <2.3391, including every detection/optimization/query cost. Prove the exact arithmetic in Lean; never choose parameters after seeing tests without recording the revision.

## Independence and organizing route

Own `algorithm/balanced_safe_cover/`, results prefix `algorithm-balanced-cover-`, and a separate dashboard card. Do not read unfinished joint_macro or paid_cover code/proofs. The paid-cover route is exploring local multi-color splitting cores. This route instead investigates GLOBAL budget-balanced separators, decomposition certificates and constrained cover enumeration. This deliberate diversity is not a second implementation of the same unfinished generator.

Read this target first and immediately write a journal skeleton. A separate fresh X0 adversary must execute frozen controls before construction. Then use distinct proof approaches and fresh nonauthor verification under prove-protocol, staged to respect global capacity. All descendants use GPT-6.1 Sol xhigh. Preserve all earlier sources, proofs, failed attempts and frozen receipts.

## Controls and prohibited shortcuts

Freeze exact fixtures and expected values before running them; independently compute their optima and coverage. Include identical/empty/singleton cases, an actual pure-bridge case, an incompatible-triple terminal case, a wrong-topology case, a nonempty omitted-optimum cover with a successful clean twin, incorrect precut accounting, a failed half-budget claim, and a false exponent certificate. Use literal fixture receipts when citing earlier controls. Retain source and implementation lineage. Pilot runtime before extending a census.

Must not assume arbitrary approximation cuts preserve an optimum, independent mark penalties add, a small kernel lowers the exponential base, or cheap local queries are free. Do not evaluate tau by an expensive exact solver and omit that work from generation cost. An explicit-list obstruction that requires preserving every optimum does not refute a lemma requiring just one.

An exact oracle is a test instrument only. Finite zero failures do not prove a universal generator. A counterexample to one proposed generator does not disprove the existence of some generator with the stated bounds. Retain the failed generator and witness, then change the organizing method.

## Acceptance

Keep Algorithm, Correctness and Smaller base open until their actual obligations are proved. Separate kernel-checked statements, reviewed prose, finite tests, conditional implications and conjectures. Validate genuine proved constituents in Lean with no sorry/admit/custom unproved axioms/native_decide, retain axiom audits and proposition-level false controls, and obtain fresh nonauthor source-model/interface review. Report a precise remaining lemma if the exact target cannot yet be closed, then continue a falsifiable alternative. Keep compute, artifacts and dashboard hosting local.
