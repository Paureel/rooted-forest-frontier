# Actual whole-source caller cost

This is an author source-operation argument with kernel-checked concrete
meters and bounds. Fresh nonauthor source-correspondence review is pending.
The full faster rooted-MAF algorithm and all three main milestones remain
OPEN. The accepted source files contain no custom axiom or proof escape.
The three ownership callers below use ordinary q=k−1 without an implicit rho.

## Inputs and units

The source tree S has n leaves and N constructors. The unsuppressed target
T has M constructors and m leaves. Thus N=2n−1 and M=2m−1. The lists A,B,C
contain ORIGINAL source taxon labels. Their lengths are explicit input
sizes; `ParentPartition` alone permits repetitions and does not imply that
their lengths are at most n. If they are actual nonduplicated component
lists, each length is at most n. These bounds do not require that additional
fact. Original target labels are distinct and every source label occurs in
the target when the frozen mass/geometry theorems require it. These are
explicit `WholeCall` hypotheses; the runtime inequalities themselves hold
on all inputs, including duplicate-label refusal and missing-label fallback.

A list constructor, match, scalar comparison/arithmetic operation, field
selection, Boolean operation and immutable reference copy each cost one
source operation. Traversals and allocations cost their visited/created
cells; address comparison costs the examined Boolean bits. The constants
below are upper charges for the pinned source. Computing the instrument's
own work counter is excluded. The claim concerns the original source
operations, with the meter providing a compositional upper accounting. It
is not a statement about extracted machine-instruction counts.

`xs ++ ys` copies the actual left spine and shares the right list and inner
objects. A reused output occurrence is still a separate outer list cell.
The frozen core meter accounts for nested partition construction and its
internal receipt-list copies. We add the ownership caller's outer copies.

## Original-label color construction

`ColorWork.meterContains` follows the short-circuit equality scan. Its value
is the literal `List.contains`; its source charge is at most 4(|D|+1).
For Nat labels the decidable membership used by `taggedColor` follows the
same equality scan. Its work is not constant in the parent-list length.

`meterLeafList` follows `VertexGeometry.leafList` exactly, retaining every
original target address. A target leaf scans D, selects `[[]]` or `[]`, and
charges eight additional constructor/control operations. A node maps
`false ::` and `true ::` onto the two child lists and appends them, charging

    child work sum + 8(left selected count + right selected count + 1).

Each prepend creates a new outer list cell and one Boolean-address cell;
append copies the left outer spine. The displayed charge covers both maps,
the append and fixed dispatches. `leafList_length` bounds selected count by
target constructors. At any global target size bound U≥M, the proved bound is

    meterLeafList(D,T).work ≤ 16(|D|+U+2) M.

For singleton D=[x] this is 16(M+3)M. In particular an unbalanced target is
charged for its repeated construction of longer address prefixes. The
bound applies to duplicates too; uniqueness is used for geometry semantics,
not to suppress runtime work.

`meterRegion` follows the original `region` recursion and charges at most
4(|v|+1). `meterColorLabel` evaluates the full singleton `leafList`, takes
its literal `headD []`, and evaluates that region. Its value is the literal
`VertexGeometry.colorLabel T v x`. Write

    C(T,v) = 16(M+3)M + 4(|v|+1) + 3.

A keep callback costs one; a single callback costs at most C(T,v); a joint
callback costs at most C(T,v)+C(T,w)+3. The joint callback performs TWO
literal singleton lookups, as in `4*colorLabel T v x+colorLabel T w x`.
No lookup table, cache or unit-cost arbitrary color oracle is assumed.

For a concrete triple d=(a,b,c), write L(T,d_i) for those local caps and

    K(T,A,B,d) = 4(|A|+1)+4(|B|+1)
                 + L(T,a)+L(T,b)+L(T,c)+6.

`meterTagged` scans A, scans B when needed, evaluates only the selected local
callback, and forms the literal parent tag. Its value is exactly
`taggedColor A B ... x` and its source work is at most K. The bound includes
all three local caps as a safe upper bound, without evaluating all three
callbacks in the original source. `region≤3`, `joint≤15` and `tagged≤47`
are proved for all inputs. Thus region and joint identifiers need two and
four bits; tagged identifiers need at most SIX bits. They are not the
possibly large original taxon labels.

`meterColorTree` follows the source `fromTree`. The tree projection is
literal `fromTree`; the number of callbacks equals exactly n; its color
work is exactly the sum of the n metered callback costs and is at most nK.
`meterWhole_colorCalls` gives n on accepted distinct-label input, and zero
on duplicate refusal. The frozen core's `initialCharge` continues to cover
all non-color initialization/address work, so no color call is treated as
already paid by that charge.

## Finite geometry

`GeometryWork.meterRooted` and `meterMinimal` follow the literal original
`RMAF.rootedSpan` and `minimalVertices`, including the latter's two rooted
span constructions at each visited node and its conditional recursive
construction. Output lengths are at most M. With U≥M,

    meterRooted(D,T).work ≤ 16(|D|+U+2)M,
    meterMinimal(D,T).work ≤ P(D,U)M,
    P(D,U) = (16(|D|+U+2)+16)(U+1).

The address lemmas prove |v|<m for every member of either actual span. No
suppressed-address length is substituted. Label comparisons within these
constructions receive the scalar bit factor below.

The frozen `VertexGeometry.findCommon` scans A-span vertices. Its full
meter charges address equality bit by bit, membership list traversal in B
and C, and recursive control. With every examined address length ≤U and
|Bspan|,|Cspan|≤U, the bound is 32(U+1)^2(|Aspan|+1). Both membership scans
are included even if Boolean short-circuiting can omit one. The value
projects to literal `findCommon`. Actual clique selection therefore costs
at most

    [P(A,M)+P(B,M)+P(C,M)]M + 32(M+1)^3 + 4.

This statement is restricted to the frozen clique/common-vertex selector.
The G/E pair selectors are excluded.

The joint count gate follows literal `jointColors`: `leafList D T`, map the
two actual region coordinates, then `List.eraseDups`. The meter follows
Lean 4.35's actual `eraseDupsBy.loop`, scanning its accumulator with `any`,
consing a first occurrence, and reversing the accumulator at the end. The
initial attempt to use the equivalent filter recursion was discarded before
acceptance; its failed logs remain in `dev/`. For a list of length h≤U this
actual loop costs at most 8(U+1)(h+1), including the final reverse. In this
consumer, pair equality compares two coordinates each bounded by three.
The complete joint gate costs at most

    J(D,T,v,w) = 16(|D|+M+2)M
      + [4(|v|+1)+4(|w|+1)+6]M + 8(M+1)^2 + 5.

Its value is exactly `jointColors D T v w`, including empty/leafless
regions and two/three occupied joint signatures. Only original region
construction and this count gate are charged here; choosing the pair-case
vertices from the hard-rule state remains a separate consumer.

## Actual capped generator calls

Set B0=min(q,n−1), before paying any initial hard2 separately, and write

    F(S,q) = 128(N+1)^3
      + (256((N+1)(N+2))^3+6)(B0+1)2^(B0+1),
    R(S,q) = 3·2^(B0+1),
    G(S,T,A,B,d,q) = F(S,q)+nK(T,A,B,d)+64.

`meterWhole_bound` consumes the immutable `CoreWork.generate_work_bound`
with that exact B0. `meterWhole.outputs` equals the frozen `wholeOutputs`
and its pruned count equals the frozen receipt. The frozen work proof
already covers every refused/root/duplicate/erase-refused prefix, every
successful last-level attempt followed by its pruned continuation, every
q=0 normalization/selection attempt, and all internal receipt appends.
The added 64 covers each whole-call invocation, fixed closure/parent-tag
construction and output-field/result dispatch, including refusal. It also
covers the fixed choice of the 3/4/2 color-triple descriptors. The
record bound R includes unsuccessful records as well as outputs;
therefore it also bounds each actual output-list length.

The three color triples are LITERALLY those in frozen `WholeMass.lean`:
clique (keep,v,v), (v,keep,v), (v,v,keep); chain
(keep,v,w), (keep,(v,w),keep), (v,keep,w), (v,w,keep);
diagonal the second and third chain triples. Whole ordinary q is passed
unchanged to each generator. The meter projections equal the frozen
`cliqueOutputs`, `fourChainOutputs`, and `diagonalOutputs`, with all
multiplicities retained. Let G_i denote their actual triple-specific G.
The proven total generator/outer-concatenation upper bounds are

    clique:   G_1+G_2+G_3       + 3R + 4,
    chain:    G_1+G_2+G_3+G_4   + 6R + 6,
    diagonal: G_2+G_3           +  R + 2.

For example the left-associated three-way append copies lists of lengths
h_1 and h_1+h_2, hence exactly 2h_1+h_2 cells. The four-way append copies
3h_1+2h_2+h_3. The constants count outer call/result control. The
`RuntimeAssembly` bounds add the actual clique selector or joint gate and
four further control operations. These are runtime consumers of the frozen
core bound, not just node-count or mass inequalities.

## RAM, bit cost and additive overhead

With words accommodating labels, q and counters, each source scalar
operation costs constant RAM time. For binary integers let H be one plus
the maximum input taxon/budget bit length, six color bits, and B0+4 counter
bits. The frozen node/attempt bounds justify the last term. Every charged
scalar equality, comparison, addition, subtraction and minimum costs O(H)
bit operations. Addresses already receive their list-bit traversal charge.
The joint pair comparisons have constant-size coordinates. Include input
parsing cost equal to the input encoding length.

Let s include both tree constructor counts, explicit parent-list lengths,
and the supplied target-address lengths. All the displayed color/geometry
coefficients are polynomial in s. Since B0≤n−1, the fixed 3/4/2 generator
construction costs are O(H(s+1)^7 2^B0 + input encoding length), hence
O(poly(input)2^q). Any complete serialization of nested outputs can be
charged using the frozen detached-volume bound and retains that form.

The same exact meter outputs satisfy the frozen raw rational mass bounds
3c^-4, 4c^-4, and c^-3+c^-4 under the printed `WholeCall`, occupied-vertex,
and joint-count hypotheses. These are WHOLE-source losses: the initial
two source cuts are already represented. No extra c^-2 appears. The two
endpoint branches contribute 2/c only to the complete displayed macro.
At c=233/100 the three expressions, including those endpoints, are strictly
below one (`strict_macro_margins`, kernel arithmetic).

For a recurrence with normalized child mass at most beta<1, and additive
construction work at most A·2^q, division by c^q leaves overhead at most A
because c>2. Choose K with A≤(1−beta)K. Then
beta K+A≤K; `additive_margin` proves this last inequality. Induction gives
the usual Kc^q bound once every recursive transition, decreasing budget,
input-size invariant, and base case has actually been proved. This argument
explains absorption of this construction overhead. It does not assert those
remaining complete-algorithm hypotheses.
