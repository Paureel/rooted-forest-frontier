# Frozen rank interface

All names below are in `Universal233.RankDichotomy`. The executable is the
unchanged frozen `CoreProgram.generate`. `inputRank T color` counts distinct
colors on the original input leaves with `SourceCoverage.dedupNat`.

`RankFeasible T color` is the existence of an original-label partition `bs`
passing `partitionCheck` and `pairwiseEmbeddings`, with every block
`LabelMonochromatic color` and exactly `inputRank T color` blocks. It contains
no generated-output, uniqueness, mass, trace, confluence, or optimum field.

| Claim | Exact theorem | Additional hypotheses |
|---|---|---|
| Every budget below r−1 returns literal `[]` | `below_rank_outputs_empty` | `q < inputRank T color - 1` |
| Every sufficient budget returns literal `[o]`, actual cost r−1 | `feasible_unique` | original leaves Nodup; `RankFeasible`; `r-1 ≤ q` |
| Unique output blocks equal full original color-class memberships | `feasible_unique_color_classes` | same hypotheses; membership stated for every label and every actual output block |
| Every actual output costs at least r if rank-r feasibility fails | `infeasible_cost` | `¬RankFeasible`; literal member of actual generated output list |
| Actual raw-LIST tail mass ≤2^(L−(r−1))c^(−L) | `generate_tail_mass` | rational c≥2; L≥r−1; every actual output costs at least L |
| Actual infeasible raw-LIST mass ≤2c^(−r) | `infeasible_mass` | rational c≥2; `¬RankFeasible` |

No theorem identifies literal source-cut addresses across differing normalized
representations. The paid count and literal output list are identified.

The uniqueness proof uses the completed source-coverage theorem and the actual
dyadic raw-list mass theorem. Coverage at budget r−1 gives a member with cost
r−1, because actual input-color support gives the matching lower bound.
`generate_outputs_mono` carries that actual member to larger budgets.
`rawQMass_saturated` proves the full literal list is its singleton: every entry
has strictly positive dyadic weight, including a repeated copy of the member.

The coordinator accepted this equivalent route in place of the target's
suggested forced-step construction. The original target remains unchanged;
no operational no-branching trace theorem is delivered or required by the
stated output/cost interface.

Exact import chain for the new conclusions:
`RankCost -> SourceValidity + RationalMass`;
`MinimumUnique -> RankCost`; `TailMass -> MinimumUnique`;
`ColorClasses -> TailMass`; `Regression -> ColorClasses`.
The source-validity import uses completed assembly-v1 only. The replay copies
the earlier controlled cut-module filename/import adapter unchanged. The new
control module has a filename-only `Controls -> RankControls` adapter to avoid
colliding with the frozen source-coverage controls; its proof bytes are equal.

Fresh nonauthor reconstruction and the consuming pair-case interface ruling
remain separate acceptance conditions. The complete algorithm and its three
main milestones remain OPEN.
