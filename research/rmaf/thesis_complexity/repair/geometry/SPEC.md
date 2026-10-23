# Local geometry route preregistration (2026-10-14)

Read provenance: source text Ch2 p12, Ch6 pp104–111 and117–126; page110 and118 rendered images; shared frozen controls; existing nine- and thirteen-leaf witness JSON; local-repair.md read as proposed only. No adversary implementation, recurrence route, correctness/transfer implementation, or parent implementation read.

Convention: binary rooted trees carry labelled unary rho (Ch2 p12). Active roots are treated as atomic labels; removed completed components are retained semantically but omitted from active computation. Protected incoming edges are independent of P,Q analysis credits. Full legal recursive call tree is analyzed; no universal short-circuit reachability claim.

Toolkit consulted: tools README has no rooted-forest source-rule enumerator. Existing problem evaluators are forbidden cross-route inputs for independence. This one-shot geometry checker is authored from source rules and frozen JSON controls, not a toolkit fork.

Proposed bounded adversary targets (freeze before testing):
1. Exact source cut families never cut both outgoing edges of one binary node (singleton; all-pendant edges of an active-root path; BCY endpoint plus sibling of protected uncle).
2. For F1=(a,((x,y),z)) or (a,((x,y),(u,v))), with a and its F2 sibling b protected, x outside b, a legitimate three-way s=3 A3BC on (x,y), and source depth/tie ordering, C-subtree exits past the local region have discounted empty-credit mass <=1/4 relative to C budget.
3. No zero-cost merger x,d after C and processing the other local pair. This is a separate hypothesis to challenge, not granted from finite evidence.

Failure: exact bound violation or purported legal cut of a protected edge; omitted earlier case; wrong orientation accepted; mismatch with frozen controls. Preserve failed versions. Finite no-fire is not proof.

Controls: reproduce all five frozen shared controls including nine-leaf 9/16, dead C, thirteen-leaf P=3 Q=2, live two-root case and orientation mutation/twin. In addition, a cherry with both children cut is a planted failure of unrestricted protected-sibling preservation.

Pilot: 100 random geometries first; rate from measured runs; any larger run remains bounded. Progress unit is fully checked input geometries and legal local exits, never CPU/exit status.

Gate: proof route self-grade at most CLOSED-UNVERIFIED; full claim needs fresh nonauthor exact replay and use-site composition. Lean checking must contain no sorry, custom axioms, or native_decide. Any unresolved premise stays explicit.
