# Residual-edge lifting target, version 1

This pin precedes a separate X0 adversary and all construction in this directory. The completed repair sources and receipts are immutable. The regimes below are separate claims; failure of a stronger claim does not silently weaken it.

## Conventions

Use finite rooted forests with injective vertex labels. Ordinary labels occur at leaves; the special rho label, if present, is at a component root and may have one child. Every unlabelled vertex of an input reduced binary forest has two children. Intermediate edge-deleted graphs need not be reduced. Yield discards components without labels, deletes unlabelled leaf vertices and suppresses unlabelled unary vertices, including unary roots; it retains every labelled vertex. Equality of yielded labelled forests means rooted label-preserving isomorphism, with original surviving IDs compared separately when available.

Source: Whidden 2013 thesis printed p.12 (rho and suppression), p.15 (yield, empty components, cut objective), pp.16-18 (sibling subtrees, shifting, AF/component compatibility), p.107 (inherited protection after suppression). The local PDF adds 13 to printed page numbers. No root-convention transfer is part of this target.

## Claims to attack

**L1: actual residual paths.** For a reduced forest F, actual current-edge set C and G=yield(F-C), every edge g of G has a nonempty directed path P_g of original F edges joining its endpoints. Its internal vertices were suppressed, its edges avoid C, and paths for distinct residual edges are pairwise edge-disjoint. Edges removed in empty fragments or deleted root stems need not occur in any P_g. No fictitious incoming edge is assigned to an unlabelled component root.

**L2: arbitrary choice lift.** For any R subset E(G), choose exactly one edge s(g) in P_g for each g in R. K=C union {s(g):g in R} satisfies |K|=|C|+|R| and yield(F-K)=yield(G-R). Every prescribed protected origin p_g in P_g may be chosen as s(g); no claim allows choosing an origin outside P_g, or selecting all protected origins on the same path while retaining this count. Arbitrary residual cuts, label-free fragments, absent parents and sequential composition are included. No AF or optimality hypothesis belongs in L1/L2.

**L3: projection and extension minimum.** For K containing C, project its additional cuts by R={g : P_g intersects (K-C)}. Ask whether yield(F-K)=yield(G-R) always holds and |R|<=|K-C|. With a target acceptance predicate depending only on the yielded labelled forest, define opt_C as minimum |K| among accepted K containing C, and opt_G as minimum |R| among accepted residual cuts. Prove opt_C=|C|+opt_G only after both directions and attained feasibility are established. Redundant cuts and empty discarded fragments must remain explicit. Infinity/infeasibility must be treated explicitly or excluded by a stated attained-feasibility premise.

**L4: global optimum and protection.** Let opt_F be the unrestricted accepted cut minimum. The precise candidate equivalence is opt_F=|C|+opt_G if and only if at least one unrestricted minimum K contains C. This is a hypothesis about existence of a minimum, not a claim about every child. Conditional protection consumer: if every unrestricted minimum avoids original p, the equality holds, and p lies on a residual path P_g, then every residual minimum avoids g, using an L2 lift that selects p. State the exact feasibility and AF acceptance premises. Do not call a branch promising without stating and proving the required optimum equality or minimum-existence condition.

**S_every: minimum common-subtree intactness.** In compatible finite reduced binary current forests F1,F2 with the same labels, each F2 component contained in an F1 component, suppose a complete proper pendant subtree A with at least two ordinary labels is identical in F1,F2 before further cuts. Candidate: every globally minimum actual current-F2 AF cutset contains no edge strictly internal to A. This is unreviewed. Distinguish it from **S_exists**, that at least one such minimum is intact. Do not import either as a lemma until adversarial audit and later proof/review. Forced-extension minima, inclusion-minimality and arbitrary AF cutsets are different domains.

**S_contract: contraction interface.** Simultaneously replace an identical complete pendant subtree A by a fresh labelled leaf alpha, retaining its incoming attachment when present. Investigate expansion/restriction and AF compatibility in both forests, exact cut cost, minimum preservation under S_exists, and whether every-optimum/protection conclusions require S_every or a different exchange argument. Same cluster labels without matching topology are insufficient. Contraction is a label-changing operation, separate from L1/L2.

## May assume

- Finite-tree validity, unique original vertex/edge IDs, injective labels and the explicit rho/binary restrictions, when checked or provided as hypotheses.
- Elementary finite set, list and natural-number facts with their actual Lean hypotheses and standard-axiom audit.
- Exact definitions of graph deletion, connected components, rooted label-preserving isomorphism and the minimum objective.
- A clearly stated conditional reviewed-prose lemma from the completed repair, only after identifying its exact current-forest premises and showing their relevance. Such use remains a prose import until formalized.

## Must not assume

- L1 path existence/disjointness, L2 lift equality, L3 projection, cost normalization, AF preservation, contraction preservation or S_every/S_exists.
- Global optimality of an arbitrary residual optimum, scalar branch equality without its hypotheses, or universal raw-cutset Cover.
- Protection represented by an OR flag automatically has a usable surviving origin, or that one cut can select multiple different origins.
- Existing conditional OriginalEdges or version 2 splice statements discharge their own graph premises.
- Finite agreement proves a universal statement; unrelated runtime/transfer arms may not be imported.

## Frozen controls and rejection twins

The adjacent controls.json fixes concrete graphs, cutsets and predicted exact results. Every route must execute these controls before real search. A control mismatch is a STOP-AND-REPORT event. A pin transcription error goes to ERRATA.md with the exact executed witness; version 1 is preserved. No silent parameter or convention repair is allowed.

The minimum-intactness X0 must separately enumerate all minima and report denominators for common subtrees, minima, every-optimum violations and existence failures. Search current forest components as well as whole inputs; distinguish a structural pair from an actual reached algorithm state. Graph X0 must test all origin choices for small paths and record separate unary-rho, root-absent, empty-fragment, redundant-cut and sequential cases.

## Licensed outcomes

A proof with exact graph/AF interfaces, an executed in-regime counterexample with the failed formulation preserved, or a smaller named open lemma with surrounding statements separate. A failure of S_every licenses S_exists only as a new surviving target; it does not prove it. A failure of an unguarded global-optimum assertion confirms its rejection twin and does not refute L1/L2. Use reviewed prose, conditional kernel, finite-tested and open classifications separately.

## Sequence and ownership

First separate fresh X0 graph and minimum-intactness adversaries. After their completed reports, named graph-path and restriction/expansion construction routes run without cross-reading unfinished work. Then fresh nonauthor controls, rebuild and use-site trace. At most two simultaneous children, Astra xhigh, subject to global capacity. Children own distinct subdirectories/results/cards. This parent owns the pin, integration and main card. No construction starts before the relevant X0 report is assessed.
