# Rooted MAF baseline audit — 2026-10-14

This is a bounded initial audit. It verifies the comparison theorem and its conventions. It does not certify an exhaustive absence of faster results, and is not a novelty clearance.

## Claim verdicts

| Claim pinned by the campaign | Verdict | Evidence / limitation |
|---|---|---|
| The supplied 2.3391 bound has a published source | SUPPORTED | Mestel, Chaplick, Kelk, Meuwese; arXiv v2 Theorem 17, PDF p26. Journal identity independently checked against Crossref and publisher record: JCSS 160, article 103800, September 2026. |
| This is the best bound in all publicly available work | NOT ESTABLISHED | The contemporary multi-tree kernel paper still reports it, but an earlier public thesis gives a claimed 2^k algorithm. Citation-index coverage and several full-text debts remain. |
| The campaign's component parameter matches the baseline | SUPPORTED | Baseline §2 p4 defines size as component count; §3 p5 changes internal recursion to further cuts. |
| A new edge-protection argument would automatically be novel | AT RISK | Whidden's 2013 thesis Chapter 6 already develops protected edges, a depth rule, correctness and a 2^k running-time argument. It needs an independent audit, not rediscovery. |

## Comparable problem specification

Extracted from baseline v2 §2, PDF pp3–4:

- Two rooted **binary** directed trees, with identical bijectively labelled leaves.
- The root has indegree zero and outdegree two; other internal vertices have indegree one and outdegree two. A one-leaf restriction is a singleton.
- `T[B]`: the minimal connected subtree spanning the labels in nonempty block `B`. Its root is the highest vertex in that embedding, rather than the original root necessarily.
- `T|B`: its rooted restriction after suppressing vertices of indegree one and outdegree one. Roots of components are preserved.
- A forest is a partition into nonempty blocks. Every block has the same rooted restriction in both trees, and different blocks have **vertex-disjoint embeddings in each original tree**.
- Ordinary agreement forest: no acyclicity constraint is imposed.
- **No extra rho label by default.** Footnote 2, PDF p4 says the paper does not adopt that convention; it states that its algorithm works with or without rho. A distance result using an extra labelled root must not be transferred silently to this model.
- Let `K` denote optimum components. Initial cut budget `q=K-1`. Later recursive `q` counts *additional* cuts. The fixed shift does not change the exponential base. Retain a reconstruction map for collapsed cherries and removed singleton components.

## Verified source locations and comparison recurrence

Theorem 17, v2 PDF p26: “Algorithm rMAF solves the problem rMAF in time” followed by `O*(2.3391^k)`.

The paper's statements are retrieved published results, not lemmas proved in this campaign.

| Baseline item | Locator | Budget recurrence |
|---|---|---|
| Classical cherry branching | §3.2, pp6–7 | `2T(q-1)+T(q-t)`; t=1 is deterministic, t=2 is limiting |
| Overlap splitting | Lemmas 1–2, pp7–9 | Dominated by `2T(q-1)` for a global base above 2 |
| Disjoint subproblems | Recursion rule and Lemma 3, p10 | Rooted algorithm uses constant pretest depth t=1; with at least two non-homeomorphic parts, dominating cost `2T(q-2)` |
| Rooted flanking rule 4 | Lemma 12, p18 | `T(q-1)+2T(q-2)` |
| Rooted boundary rule 5 | Lemma 13, pp18–23 | At most `T(q-1)+3T(q-2)`; its complicated case 3.2.2 reaches the larger flanking factor |
| Deterministic single-edge overlap rule | Lemma 14, pp23–24 | `T(q-1)` |
| Isolated homeomorphic overlap group | Lemma 15, p24 | Fitch optimization, `T(q-1)` if a cut is needed |
| Global rule order | Figure 16, p24 | t=1; t>=3; rule4; rule5; t=2 with rule6/7; exhaustive SPLIT; decomposition |
| Limiting composite | Lemma 16, pp25–26 | `2T(q-1)+T(q-3)+2T(q-4)` |

The `2T(q-1)` terms in the limiting composite isolate the two cherry endpoints. The two-cut branch needs a post-branch bound `T(q-1)+2T(q-2)`. Lemma 16 handles overlap and topology cases to obtain this improvement. Its source proof is read, but it has not been formally reconstructed here.

For the limiting recurrence the characteristic equation is

`2/c + 1/c^3 + 2/c^4 = 1`, equivalently `c^4-2c^3-c-2=0`.

The retained exact arithmetic receipt shows a sign change between 2.3390 and 2.3391, and that 2.3391 is a valid upper base. At c=23391/10000, the characteristic polynomial is `7443792512161/10^16 > 0`. A deliberately lower upper-bound claim at c=2339/1000 fails. These checks use exact rational/integer arithmetic, not approximate roots. They validate the arithmetic conditional on the recurrence; they do not validate the structural recurrence or supply a Lean proof. The coordinator's independent Lean route must audit this separately.

**Cost-interface qualification (inference, not a published erratum).** Lemma3 p10 states domination by `2T(q-(t+1))`, but its proof's `p=1` case has `T(q-1)`. At t=1 and a global model `T(q)=c^q` with c>2, that is larger than `2T(q-2)`. The safe combined bound is `max(T(q-1),2T(q-2))`, rather than silently substituting the two-call case everywhere. This does not by itself refute Theorem17: in Lemma16 the required post-branch budget bound is `T(q-1)+2T(q-2)`, which also covers direct `p=1`; after one overlap cut, the `p=1` cost becomes `T(q-2)`, also under that target. A full rederivation should explicitly retain both decomposition cases. This audit has not asserted a certified repair or a flaw in the final 2.3391 theorem.

## Later work and the earlier 2^k claim

1. **Kelk, Meuwese, van Iersel, arXiv:2602.22281v3 (2026-06-11)**: full 23-page text read. Introduction p2 still gives 2.3391 for two rooted trees. Its new result concerns kernels for multiple trees. The rooted kernel is Theorem 2, p19, using chain truncation `r=min(max(K,3),t+1)`; it does not claim a smaller two-tree branching base. Its v3 fixes earlier tightness examples, so v1/v2 must not be substituted.
2. **Whidden, PhD thesis (July 2013)**: source has 214 PDF pages; front matter, Chapter 2 definitions (printed pp12–18) and all of Chapter 6 (printed pp100–127) read. Theorem 6.1/Corollary 6.2 on p100 claim O(2^q n) for rooted SPR distance. Theorems 6.12 and 6.13 give correctness and cost arguments on pp114–126. Protected edges exclude duplicate branches; a depth rule and special configurations support the cost argument. This is a substantial prior argument, not merely a software README claim. It has **not** been independently reconstructed or validated in Lean. Other thesis chapters and imported lemma proofs remain unread.
3. **Root convention in that thesis**: Chapter 2 p12 adds a labelled root rho with one child and includes rho in X; p15 gives distance = augmented MAF components minus one. Therefore its comparison to unaugmented ordinary MAF requires explicit treatment. Neither validity nor invalidity of the 2^q argument is concluded in this audit.
4. **Whidden's official rSPR repository**: README Efficiency section claims O(2^q n), and Citing rSPR refers to the corresponding paper as “In Preparation” (2013). The baseline v2 p2 footnote 1 itself acknowledges a further advancement in the thesis that remains unpublished. This supports describing 2.3391 as the checked peer-reviewed comparison baseline; it does not support saying no faster public claim exists.

## Search coverage, debts, and replay

24 keyword queries were executed, including the explicit current year 2026; query receipts are in `baseline-search-ledger.json`. A primary author publication page and institutional author/repository pages were swept for the baseline authors. The forward chain `Split-or-decompose -> 2026 multi-tree kernel` is checked from the later paper's reference 13, p23. The baseline's complete reference list was read and relevant ancestors recorded as debts.

Semantic Scholar's public API returned HTTP429. OpenAlex returned zero citations for its journal record, although the independently read kernel paper cites the baseline. This is an observed indexing limitation, not evidence of no citing work. Google Scholar's cited-by chain, journal TOCs, zbMATH/MathSciNet, and the full synonym-family re-sweep were not completed. Searches are **not dry**: the PACE primary literature list surfaced a 2020 practical exact paper which remains full-text unread. The final journal PDF (19 pages) was not compared line-by-line against the 27-page arXiv v2.

Replayable next actions, in order:

1. Independently reconstruct Whidden Chapter6, including Chapter3/imported lemma obligations and root-convention conversion; preserve all actual counterexamples or failed proof obligations. Do not label it false because it was never journal-published.
2. Obtain/read `Faster Exact Computation of rSPR Distance via Better Approximation`, DOI10.1109/TCBB.2018.2878731, and the 2015 `Faster exact computation of rSPR distance`, DOI10.1007/s10878-013-9695-8.
3. Complete legitimate forward-citation indexing and author recency sweeps through 2026-10-14; inspect PACE2026 exact solver descriptions for theorem claims, not benchmark speedups.
4. Read the 9q-3 rSPR kernel source arXiv:2202.09904 before importing its reductions. Inspect the chain-reconstruction conditions separately.
5. Re-sweep new works until a fresh round yields no new P3+ candidate and no named channel has died on access/budget. Only then consider a stronger latestness/novelty verdict.

## Tool and verification provenance

The BootLoops capability index was consulted. No installed instrument audits this particular recurrence/model; no new solver was written. PDF extraction used the bundled pypdf; extraction-missing thesis pages121/123/131 were rendered with bundled Poppler and visually read. Exact recurrence arithmetic uses Python Fraction plus an integer-numerator identity cross-check; this is shared-arithmetic evidence, not an independently certified theorem. Source bytes, Crossref response, OpenAlex responses, arithmetic receipt, hashes and read locators are retained under `sources/baseline/`.
