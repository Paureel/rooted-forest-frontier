# Whole-source work: bounded semantic review

The literal color and output projections support the stated 3/4/2 caller accounting. The source-operation claim needs a corrected correspondence: the formal meter's outer append charge counts copied cells, whereas the preregistered source contract allows eight primitive operations per copied cell. A conservative source envelope preserves the claimed polynomial-times-`2^B` form. This review does not establish a complete recursive algorithm, selector-to-dispatch integration, or a machine-time bound. All three main milestones remain OPEN.

This is a bounded semantic child of the existing reviewer, with zero additional independent replications. The parent supplied the proposed corrected envelope after its own reading; the block-by-block scrutiny below is this child's inspection of the permitted released files. No replay, compilation, census, author contact, other completion review, or new child was used. The source identities are those pinned by the parent release; this child did not independently re-pin or audit the package. Claims about successful kernel replay belong to the parent's retained replay, not to this receipt. Raw `Geometry.lean`/`RMAF.lean` definitions were outside this child's permitted reading, so the parent must retain its own opened-definition inspection of the operational source relation.

## Read facts and consumer premises

All Lean locators below refer to `../isolated/`. The permitted author prose is `universal233/whole_source_work/COST-MODEL.md` and `RESULT.md`. The frozen reference inputs are `../OPERATION-SPEC.md`, `../COST-BOUNDARY-AMENDMENT-v1.md`, and `../frozen-inputs/CORE-COST-CORRESPONDENCE.md`.

| Read fact | Source and load-bearing text | Consequence |
|---|---|---|
| Literal parent encoding | `WholeColors.lean:14–15`: `if x ∈ A then 3 * ca x else if x ∈ B then 3 * cb x + 1 else 3 * cc x + 2` | Parent identity is the residue modulo three. The preregistered reference encoding is related by decoding, not literal numeric equality. |
| Literal joint encoding | `OriginalColors.lean:6–7`: `4 * colorLabel T v x + colorLabel T w x` | Both original singleton target lookups are required. No cache or unit-cost oracle follows from the finite color range. |
| Original lookup and fallback | `ColorWork.lean:124–131`: `meterLeafList [x] T`, then `meterRegion v (a.value.headD [])`, with value projection | The full target traversal and original addresses are charged, including missing-label fallback to `[]`. Proper-target-label premises are needed for geometry interpretation, not for this value projection. |
| Local and tagged ranges | `ColorWork.lean:185–193,237–244`; local range at most 15 and tagged range at most 47 | Local region, joint and parent-tag values require at most 2, 4 and 6 bits. This says nothing about original taxon-label width or evaluation time by itself. |
| Selected callback only | `ColorWork.lean:204–216`: scan A, then B when needed, then one selected `meterLocal` | Summing all three local caps in `taggedCap` is conservative. It does not mean the original source evaluates all three local callbacks. |
| Exact descriptor association | `OwnershipWork.lean:118–137`, `WholeMass.lean:79–82,105–109,140–142` | Clique uses `(keep,v,v),(v,keep,v),(v,v,keep)`; chain uses `(keep,v,w),(keep,joint(v,w),keep),(v,keep,w),(v,w,keep)`; diagonal uses chain entries two and three. Each call receives unchanged q. |
| Raw outputs retain multiplicity | `OwnershipWork.lean:139–149`; `WholeMass.lean:79–84,105–112,140–145` | The lists are literal append results, including repeated equal outputs. There is no raw-output deduplication step to charge quadratically. |
| Original conversion callback count | `OwnershipWork.lean:30–41,80–84` | The recorded color-call field is n on accepted distinct-label input and zero on duplicate refusal. It is a projection of original-source accounting, not an execution count for the instrument itself. |
| Target-bounded joint dedup | `GeometryWork.lean:174–215,244–269` | Dedup scans the accumulator and reverses it. Its input has at most M selected target leaves, so its quadratic cost is polynomial in input size. The generic BEq meter alone does not bound arbitrary equality implementations. |
| Clique selection is limited | `GeometryWork.lean:435–451`: “Only the frozen clique/common-vertex selector is included.” | Original spans, original address lengths, and findCommon are included; G/E pair selectors and hard-parent history are excluded. |
| Mass premises are explicit | `WholeMass.lean:8–18,85–89,113–119,146–151` | Parent support/disjointness, target distinctness, source-label support and nonempty parents are required through `WholeCall`; clique needs three occupied premises, chain needs four occupied premises and joint count at least three, diagonal needs outer occupied premises and joint count exactly two. |

`ParentPartition` gives membership cover and pairwise disjointness, not list Nodup (`WholeColors.lean:8–12`). Thus parent-list lengths remain explicit input sizes. An arbitrary vertex supplied to a runtime inequality need not be occupied or even selected. The runtime inequalities alone cannot discharge the displayed mass hypotheses.

## Meter/source distinction and the append correction

`OwnershipWork.lean:114–116` assigns `a.work+b.work+a.outputs.length+2`. Its `copied` field records the same left-spine cell count. This is a valid formal definition of a meter; one copied list cell is not every match, reference move and constructor named by the source convention at `COST-MODEL.md:22–29`. The frozen `OPERATION-SPEC` requires a conservative multiplier eight per copied cell. The previously accepted core correspondence already repaired the analogous internal receipt-list charge, so the consumer must carry that repaired core envelope forward, rather than promote `generate_work_bound` alone into source-cost certification.

For actual output lengths h_i, left association copies exactly `2h1+h2` cells for clique, `3h1+2h2+h3` for chain, and `h2` for diagonal. With each h_i at most `R=3*2^(B+1)` (`OwnershipWork.lean:98–110`), the source copy charges are at most `24R`, `48R`, and `8R`. Allowing sixteen fixed operations per outer append gives bases 32, 48 and 16. Inner refusal and output receipt copies remain in the corrected standalone core bill; these outer source callers append outputs only.

These corrections identify a failure of the direct meter-unit/source-unit correspondence. They are not a counterexample to the very large displayed total bound: unused slack elsewhere might pay the difference, but that would need its own domination argument. The formal meter inequalities at `OwnershipWork.lean:171–208` continue to mean exactly what their definitions state.

## Conservative source envelope by inspection

Use the frozen ordinary immutable-list contracts: at most eight primitive operations per copied left-spine cell or inspected Boolean-address bit, with explicit fixed list bases; nested objects are shared. For the following new helpers, a factor 64 on their positive assigned charge is conservative. This is a source-block inspection argument under those contracts, not a kernel-extracted execution trace or a newly executed quantitative check.

| Source block | Assigned local charge | Inspection bound supporting factor 64 |
|---|---:|---|
| Nat contains | 1 at empty, 4 per scanned cons | At most sixteen fixed match/equality/branch/reference operations per scanned cell and eight at the base. Nat equality receives the scalar bit factor separately. |
| Region/address equality | 2 at base, 4 per examined bit | At most sixteen fixed operations per pattern/bit step or base; no whole-address comparison is hidden as one unit. |
| `leafList` maps and append | `8(a+b+1)` | Two prepend maps cost at most sixteen per selected item; left append adds at most eight per left item. The fixed node/maps/append bases fit forty. Thus `24(a+b)+40` is below 64 times the assigned local charge. |
| Rooted/minimal span local construction | `8(a+b+2)` or `8(h+2)` | The same maps/copy allowance and at most sixty-four fixed operations fit. Both rooted child constructions and any conditional recursive minimal construction are separately present in the meter. |
| Color-label/local/tag arithmetic | +3, keep 1, joint +3, tag +4/+6 | `headD`, dispatch, fixed reference moves and multiplication by 3 or 4 plus residue addition fit at most thirty-two operations per local block. A joint has two separately charged color-label calls. |
| Joint map | +6 per selected input, base 1 | Pair and outer-cell construction plus dispatch fit thirty-two; both region recursions are separately charged. |
| Joint dedup | 4 per equality scan, +4 per input, final `4(|acc|+1)` | With coordinates at most three, a pair equality and scan control fit thirty-two operations; final reverse fits eight per cell plus sixteen at base. This does not certify generic arbitrary `BEq α`. |
| Vertex membership/common scan | +4/+6 per item, empty 1 | Address equality and both membership scans are separately charged. Fixed match/branch/reference control fits thirty-two. Charging both scans is safe when the source short-circuits one. |
| Selector/gate assembly | +4 | At most thirty-two fixed dispatch/reference operations; child bills are already separate. |

These bounds deliberately overcharge recursive reference passing and all fixed dispatches. The released meters represent two original lookups for a joint, both target children, both rooted subtrees used by minimal, the chosen minimal continuation, both common-vertex membership scans, and the accumulator/reverse dedup path. No repeated callback is omitted in those meter definitions by treating the color range as a runtime bound. Extending this block argument to the original imported definitions requires the parent's separate source inspection: a value projection alone would not prove that a pure source expression evaluates or shares a recursive subresult only once.

Let F be the accepted corrected standalone source envelope from `CORE-COST-CORRESPONDENCE.md`, with `B=min(q,n−1)`, not merely the formal core meter theorem. Let K_i, selectionCap and jointGateCap be the released meter bounds. A transparent conservative replacement is

    G_i* = F + 64*n*K_i + 4096.
    Clique source <= sum_i G_i* + 24R + 32.
    Chain source <= sum_i G_i* + 48R + 48.
    Diagonal source <= G_2* + G_3* + 8R + 16.

The 4096 per call pays the finite descriptor tuple/closure creation, whole-call/result projection and fixed invocation control without using an oracle-cost assumption. Add `64*selectionCap+256` for the clique selector or `64*jointGateCap+256` for the joint count gate and its fixed wrapper. All new helper caps are polynomial in tree sizes, parent-list lengths and supplied original-address lengths. The corrected F has degree at most seven times `2^B`; R is a constant multiple of `2^B`. Therefore these corrected constructions retain `O(poly(input)*2^B)` and hence `O(poly(input)*2^q)` structural source work. This is a derived conditional bound, not a finite-test inference.

For scalar bit cost, retain the input label/budget widths, six color bits and capped search-counter widths. A safe explicit H also covers any evaluated size/count scalar widths, bounded by `log2(s+1)` for the input-size parameter s, and any chosen implementation's pointer-width costs if those are counted as bit operations. Multiplication by fixed 3 or 4 is linear in scalar width. A machine RAM claim still needs words large enough for stored values and references; compiler transformations, allocation/GC and cycles have not been verified here.

## Instrument execution and open integration

`meterWhole` runs `meterGenerate` and also constructs `init` with `meterColorTree` on accepted input; its refusal branch syntactically contains `fromTree` with zero recorded calls (`OwnershipWork.lean:68–73`). Running this definition is an instrument computation with duplicate source-like work and potentially unused-tree evaluation. Its `colorCalls` field is not a dynamic trace of that computation. The claimed n/zero counts and corrected source bound concern original `wholeOutputs`, whose output projection is explicit at `OwnershipWork.lean:75–78`. Reporting instrument execution as original runtime would require an additional implementation/cost theorem, including the treatment of unused values.

`RuntimeAssembly.cliqueConstruction` adds selection work while taking an independently supplied v (`RuntimeAssembly.lean:8–9`). There is no equation binding v to the returned `some v`, and no none-case caller here. The chain/diagonal quantities likewise add the joint gate but do not test its result or select a macro (`:11–15`). These are useful additive accounting quantities for supplied vertices. Actual selector-result-to-v and joint-count-to-chosen-macro dispatch are still open consumers, alongside the excluded G/E pair selector and hard-parent/refinement history.

`strict_macro_margins` and `additive_margin` (`RuntimeAssembly.lean:47–75`) state conditional arithmetic. They do not provide actual child transitions, decreasing budgets, state-size invariants, base cases, termination, reconstruction or output coverage. The mass statements consume the explicit hypotheses above and apply to raw lists with multiplicity; no extra initial hard2 payment or implicit rho is introduced. A complete exponent theorem and novelty acceptance do not follow. All three main milestones remain OPEN.
