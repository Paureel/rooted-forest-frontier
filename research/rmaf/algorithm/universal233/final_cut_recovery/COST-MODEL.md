# Final recovery work

The final recovery runs once after a minimum labelled agreement P has been selected. Its source-operation bound is polynomial(n, labelbits) times 2^(|P|-1). The source-operation correspondence is a mathematical argument by inspection of the pinned executable definitions. Lean checks the value projection, color-scan bound, complete-generator envelope composition, exact cost substitution, and rational-base absorption. This is the same helper-versus-fine-operation qualification as the completed CoreWork package; it is not an extracted machine-instruction trace. Fresh nonauthor source-cost review is pending.

Let N be the number of source tree constructors, n its number of leaves, p=|P|, and M=P.flatten.length. The guard charge is

    G = 4096 (N+M+p+2)^8.

This expression also accounts for rejected arbitrary inputs; for such inputs M and p need not be bounded by n. On accepted input, `checked_flatten_perm` proves M=n and `blocks_le_flatten` proves p<=n. The tree is binary, so N=2n-1. The rank/separation proof gives p>=1.

We use the CoreWork source-operation convention: list constructor, pattern match, field access, immutable reference copy, Boolean test and scalar arithmetic/comparison each have unit source charge. List traversal and copying count their cells. Address equality counts inspected Boolean cells. Each scalar operation is converted to bit operations below. The instrumentation's own evaluation is excluded from the program cost.

The following bounds explain G. Write s=N+M+p+2, so s>=3. Constants allow matches, tests, allocation and list traversals in addition to the displayed predicates.

| Actual guard helper | Conservative source upper bound | Reason |
|---|---:|---|
| `leaves`, source `Nodup` | 128s^3 | At most N tree visits and n-sized append traversals per visit, followed by at most n^2 label comparisons; repeated literal leaf-list construction fits the same allowance. |
| `partitionCheck` | 128s^3 | Nonempty tests visit p blocks. Each source-label count may rebuild `P.flatten`, then scan M labels. The final subset check scans M labels against at most n source labels. Both successful and failed short-circuit guards fit the full scan. |
| one `rootedSpan b S` | 64s^4 | At most N leaf membership scans, each of length at most M. Each returned original address has at most N bits, and list maps/appends have at most N entries at every tree constructor. Charging all intermediate address/list construction gives a polynomial of degree at most four. |
| one `minimalVertices b S` | 256s^5 | Its recursive descent has at most N calls. At each call both literal rooted spans are computed. Its output lists at most N original vertices, with at most N bits per address. |
| one `disjointVertices` comparison | 32s^3 | At most N outer addresses, each compared with at most N addresses; each address equality inspects at most N Boolean cells. |
| all `pairwiseEmbeddings S P` | 1024s^7 | At most p(p-1)/2 comparisons, each with two minimal-vertex computations, one disjointness scan, and list/control overhead. Recomputations are included; no caching is assumed. |

The sum and the remaining Boolean/control operations are below 4096s^8. The size arguments for rooted spans and minimal embeddings follow directly from their literal recursion: each output address names a vertex in the current original subtree, and prepending a side preserves this property. In particular the calculation counts intervening unary path vertices before suppression.

The program represents a block's color by its first original label. `blockColor` scans blocks in literal input order. In a visited block its `contains` call inspects at most the block length; a successful scan reads `headD` and stops. `meterColor` follows the same contains test and early stop, and its value projection equals `blockColor` universally. Its full visited-block charge is at most

    32(M+p+1)

per lookup, as proved by `meterColor_work`. `total_color_work` sums the actual color charges over any literal input label list. The core's `meterGenerate_calls` proves exactly n initial color calls on accepted input and none on repeated-source-label refusal. Therefore

    C = 32n(M+p+1)

covers all color evaluation. There is no separate color table or partition enumeration. Colors copy existing labels, so their bit lengths never exceed the original label maximum.

The completed core envelope includes initialization, all evaluated prefixes, both attempted branches, root/duplicate/erase refusals, zero-budget pruned continuations, output construction, actual left receipt-list copying, and all counter operations. We use it at B=min(p-1,n-1). Its operation bound is

    I + (A+6)(B+1)2^(B+1),
    I=128(N+1)^3,
    A=256((N+1)(N+2))^3.

Accepted P gives B=p-1. The wrapper selects `outputs.head?`, so final extraction costs a constant operation. It performs no output-equivalence scan. Uniqueness is a theorem used to establish the returned certificate, and does not delete any prefix from the work calculation. Outputs and cuts remain immutable references. If the caller serializes the final certificate, its p-1 original addresses each have at most N bits and its partition has n original labels; that extra polynomial term fits G.

`meterRecover_value` proves that the instrument's value is exactly the executable `recover`. `final_work_bound` proves the total charge is at most

    F(S,P) 2^(p-1),
    F(S,P)=G+C+I+1+2(A+6)p.

For accepted input, F is O((n+1)^8). `final_work_actual_cost` rewrites the exponent to the returned original cut-list length. `final_work_absorbed` proves the rational statement F*2^(p-1)<=F*c^q whenever c>=2 and p-1<=q, including c=233/100. The real-base inequality follows by the same elementary power monotonicity. This is an additive bill for one final call; the search recurrence is a separate obligation.

Let L be one plus the largest original-label bit length. The selected budget is p-1<=n-1, so it needs O(log(n+1)) bits. Core receipt counters need O(n+1) bits, using the completed all-prefix bound. Direct Nat comparison/addition/subtraction converts source operations with an O(L+n+1) factor. Input parsing is linear in its encoding length. Thus the accepted final recovery has bit cost

    O((L+n+1)(n+1)^8 2^(p-1) + input_encoding_length).

No wall-time measurement is used as a complexity proof. The only measured timings concern local proof compilation and determine the bounded replay plan.
