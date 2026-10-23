# Work bound for the frozen source generator

This note proves a source-operation bound for the immutable `CoreProgram.generate` and states its RAM/bit interpretation. The Lean evaluator has exactly the frozen receipt as its value projection. The source-operation correspondence below is a mathematical proof by inspection of the pinned program; the Lean kernel checks the size invariants, helper charge bounds, actual receipt-copy recurrence, and capped generator bound. This is an author result pending fresh nonauthor review. The complete faster rooted-MAF algorithm remains OPEN.

Let n be the number of input leaves, N the number of binary-tree constructors, q the supplied budget, and B=min(q,n−1). Thus N=2n−1. In the source-operation model below, the generator's work excluding evaluation of its arbitrary color function is at most

    128(N+1)^3 + (256((N+1)(N+2))^3+6)(B+1)2^(B+1).

The bound counts duplicate-label refusal, all unsuccessful/root/duplicate/erase-refused attempts, all zero-budget work and pruned continuations, output construction, and materialized output/refusal-list concatenation. Consequently the source work is O((n+1)^7 2^B). On accepted inputs the initial conversion makes exactly n source calls to `color`; on duplicate-label refusal it makes zero. Add their actual evaluation costs separately. An arbitrary `Nat → Nat` function has no unconditional polynomial evaluation bound.

## Source-operation convention

A list constructor, match, field selection, immutable reference copy, Boolean test, scalar Nat equality/comparison, scalar Nat addition/subtraction, and scalar control operation each cost one source operation. Address equality stops after the first unequal bit or list end; it inspects at most the shorter Boolean-list length plus one, with a fixed number of operations per bit. Traversing, copying, filtering, mapping or finding in a list costs its visited cells plus allocated cells and the separately charged predicate operations. Immutable `xs ++ ys` copies the left spine and shares the right list and element objects. A scalar-operation-to-bit factor is stated below; Nat values are never asserted to have bounded machine-word size.

The constants in `groupsWork`, `normalizeWork`, `eraseWork`, `findFilterWork`, and `allWork` cover the match, allocation and predicate operations in this convention. Each is an upper charge, so an optimized compiler may perform less work. The charge does not include the time spent computing the instrumentation itself. The runtime claim concerns the frozen generator.

## Stored sizes

`footprint` counts every current tree constructor, every stored label-list cell and every stored original-address bit. It excludes scalar Nat encodings. `normalize_footprint` and `erase_footprint` prove that normalization and successful erasure cannot increase it. `fromTree_footprint` proves

    footprint(fromTree color p t) ≤ N(|p|+N+2).

In particular the initial footprint S is at most N(N+2), independently of color values. `group_size`, `groups_length`, `payload_length`, and `groups_flatMap_payload` bound every selected group's labels/address, the group-list length, and the current flattened label count by S. These are syntactic size statements and use no cut-component realization.

`Payload.Prefix` uses the literal chooser, both attempt guards and literal erasure. Its induction proves that a successful prefix at depth d has at most S current footprint, exactly d detached groups and d cut records, detached constructor/label/address volume at most dS, and each stored cut address at most S bits. Actual evaluated prefixes have d≤B. A successful attempted child at the last level has d≤B+1 and is still covered before its pruned continuation. Thus even these temporarily materialized states have polynomial size. No unexamined detached payload is treated as a scalar encoding.

The formal resource condition `Within m q t d c` is the numerical invariant

    footprint t + |d| + |c| + 2q ≤ m.

`continuation_within` proves preservation at every successful literal erasure as the remaining budget decreases. `initial_within` takes m=N(N+2)+N+1, since 2B≤2n=N+1. This condition has no field assuming a runtime bound or a simulation theorem.

## Local source correspondence

Write s for the incoming current footprint, a for the detached count and b for the cut count. Normalization has footprint at most s. The following table accounts for one actual call to `step`. We include both possible attempts and finish construction in the upper charge even though a call uses only one branch.

| Frozen source operation | Source upper charge | Reason and formal evidence |
|---|---:|---|
| `normalize current` | (s+8)s | `normalizeWork` adds the actual left payload length for every homogeneous append; `normalizeWork_bound`, `gNodes_le`, `normalize_footprint` |
| `choose`: `groups t` | (s+5)s | `groupsWork` includes actual left group-list lengths; `groupsWork_bound` and group length ≤s |
| `choose`: all colors equal | 2s+1 | Short-circuiting `allWork_bound` |
| `choose`: `find?` with full `filter` and `length` predicates | (8(s+1)+2)s+1 | Each visited candidate scans the whole group list; `findFilterWork` retains the actual successful predicate stop, and `findFilterWork_bound` checks the sum. Filter allocation and its result's length traversal are included. |
| `choose`: `mixedCherry`, result match and color test | 4s+15 | Full-tree bound includes both arguments of `Option.or`; no compiler laziness assumption |
| each attempted child: root and `contains` guards | (b+1)(s+8) | Every selected group's origin length is ≤s by frozen chooser occurrence lemmas plus `group_size`. Root test is constant, and at most b address comparisons scan at most s bits each; the charge includes their list traversal and fixed comparison operations. |
| each attempted child: literal `erase` | (2s+8)s | Full source traversal including address comparisons, both subcalls, option matches and suppression; `eraseWork_bound`. Guards/early deletion can reduce it. |
| each attempted child: cons/update/refusal and control | 8 | Two constant-time cons cells, result/refusal construction and counter update; zero-budget continuation is separately charged below |
| finish: second `groups`, current `flatMap`, detached map/append and output | (s+5)s+8(s+a+1) | Second group traversal included; flattened payload ≤s; `detached.map Group.labels` visits a groups and shares their inner label lists; the outer append copies a cells; fixed output/cut references are included |
| remaining `step`, `prefixRoot`, `combine` fixed fields/counters, budget dispatch | 24 | At most three counter additions in combine, one prefix addition and the fixed constructor/match operations; no output/refusal spine copy is included here |

The sum is exactly `sourceLocalMajorant s a b`. `sourceLocalMajorant_bound` and `primitive_sheet_le_localCharge` prove that it is at most

    localCharge = 256(s+a+b+1)^3.

The helper charges explicitly account for label-copy, group-copy, filter/length work and original-address comparisons; they do not replace those operations by unit time. The correspondence between the finite table and the source statements is the proof-by-inspection part of this result. A reviewer can check it directly against the frozen `CoreProgram.lean` definitions. The Lean theorem does not claim an extracted machine-instruction trace.

## Recursive receipt materialization

`meterAttempt`, `meterStep` and `meterRun` reproduce every guard, erase call, branch and receipt field. `meterRun_receipt` and `meterGenerate_receipt` prove equality to the frozen `run` and `generate` for every input, without an assumed simulation. At a binary branch, the instrumentation adds

    |left.outputs| + |left.refusals|

to both the work and copy count. Appended objects are immutable references; their nested partitions are created at terminal steps and remain shared. Thus an output can be copied again at every ancestor. `run_records_events` and `run_records_bound` bound the number of records in each returned subtree, including attempt refusals. Duplicates are retained as separate records.

A successful zero-budget attempt still performs normalization, choosing, guards, erasure, group/cut cons and the pruned continuation. Each such continuation costs one extra operation. `meterRun_pruned` proves that the number of these calls is exactly the frozen `Receipt.pruned` counter. All attempted children are already included by the source's child-attempt bound.

If L bounds all local charges under the preserved resource condition, `meterRun_bound` proves the honest recurrence

    E(0,L) = L+3,
    E(j+1,L) = L+2E(j,L)+3·2^(j+1).

At budget zero, the extra three cover two successful pruned continuations and one possible refused left record copied at combine. At larger budgets the last term bounds the complete left output/refusal list, including failure records. `envelope_closed` proves E(j,L)≤(L+6)(j+1)2^(j+1). The extra j+1 factor is retained when B grows; combine is never assumed constant-time.

## Initialization and the final formula

The source's first `leaves` builds the label list for `Nodup`; the accepted branch may build `leaves` again for its length. Each tree leaf-list build makes at most N append traversals of at most n cells, with at most a fixed number of operations per visited/copied cell. Deciding `Nodup` uses at most n(n−1)/2 scalar label comparisons and quadratic list traversal. `fromTree` traverses N constructors, appends one address bit at each child call and stores one leaf label per leaf. Every address has length at most N. Its non-oracle work is O(N²). The cap uses one minimum, one subtraction and the bounded length. The roomy `initialCharge=128(N+1)^3` exceeds their combined source charge. Duplicate-label refusal also fits it.

`meterFromTree_tree` proves the conversion's value is exactly `fromTree`; `meterFromTree_calls` proves the call count equals n. `meterGenerate_calls` proves the accepted/refused split. `generate_work_bound` consumes `initial_within`, the local cap, the preserved resource and the materialization recurrence. Substitution of m=N²+3N+1 gives the displayed bound, since m+1=(N+1)(N+2).

## RAM, bit costs and output writing

For a word RAM whose words accommodate the scalar labels, stored colors, budget and receipt counters, the source bound converts to time by a constant factor. If these values are variable-length binary integers, let H be one plus the largest bit length among input labels, returned colors, the supplied budget and 2^(B+3). Boolean-address work is already counted by list length. Equality, comparison, addition, subtraction and minimum on these integers cost O(H) bit operations using direct representations. All receipt counters are bounded by the number of recursive nodes/attempts, O(2^(B+1)); therefore B+O(1) counter bits suffice. Bound input parsing by the input encoding length, and add the actual n oracle-evaluation costs. The time bound is

    O(H(n+1)^7 2^B + input_encoding_length + sum_x color_evaluation_cost(x)).

For the ownership callers with at most five color identifiers, C≤3 color bits suffice after identifiers are fixed. A finite table of n input labels and colors gives lookup cost O(nH) per color call under a linear scan, hence at most O(n²H) for all n calls. A direct indexed array on canonical labels gives O(1) RAM lookup. Both choices make the external oracle bill polynomial without restricting `CoreProgram.generate`'s function type. Large original Nat labels are covered by H.

The generator materializes the result as immutable lists. If a caller serializes every nested output afresh, the detached-volume bound gives at most O((B+1)S) stored label/address cells per output, and there are O(2^(B+1)) records. Adding O(H(B+1)S2^(B+1)) bit work for full serialization preserves the same polynomial-times-2^B bound. Literal refusal strings come from a finite fixed set and have bounded size.

## Remaining consumer

The result supplies the standalone original-source generator work bound. The next runtime consumer must instantiate the ownership-prefix colors, charge any color-table construction, and sum this bound over actual generated ownership prefixes with their remaining budgets. It must then compose the relevant pair/refinement operations and prove the claimed complete exact algorithm below 2.3391 under q=k−1, with no implicit rho. Fresh nonauthor source-cost review is also pending. None of the three main algorithm milestones is changed here.
