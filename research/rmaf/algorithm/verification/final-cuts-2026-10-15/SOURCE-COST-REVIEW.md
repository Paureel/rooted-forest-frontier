# Final-call source-cost inspection

CONFIRMED-SCOPED: under the explicit ordinary immutable-list and scalar contracts carried from frozen-inputs/CORE-COST-CORRESPONDENCE.md, final source recovery has a polynomial source factor times2^k, k=|P|-1. The kernel separately proves meter/value and bound algebra. No pointwise equality between the meter and every fine operation, extracted machine/GC instruction count or global solver runtime is accepted. The earlier helper79-versus86 and append-cell multiplier8 correction remains in force; its reuse is the same checker lineage, with zero extra replications.

## Actual operations

RecoveryProgram.inputCheck computes source-leaf distinctness, the literal partition checker and original minimal-support embeddings. Source operations are charged for all full helper traversals; short circuits can reduce work. RecoveryProgram.recover then scans P.length and subtracts1, calls actual generate once on ORIGINAL S, and selects head?. No runtime inputRank, BlockPermutation check, partition enumeration, target-agreement check, graph-component materialization or local-cut union is executed. Those logical properties enter through proofs. The instrument's own guardCharge/finalPolynomial/meter computations and reviewer graph/diagnostic work are excluded from production code cost.

Write N=treeNodes(S), n=|leaves(S)|, M=|P.flatten|, p=|P| and s=N+M+p+2>=3. The frozen guard envelope is G=4096s^8, including refusal. Independent inspection of the actual RMAF source supports the author's conservative table: two leaves constructions and Nodup fit128s^3; nonempty/count/subset partition checks fit128s^3, including rebuilding flatten within each source-label count; one rootedSpan fits64s^4 including all original unary paths and list/address allocations; one minimalVertices fits256s^5 because at most N recursive calls recompute both rooted spans; each disjointVertices comparison fits32s^3 because at most N-by-N original address comparisons inspect at most N bits. The at-most p(p-1)/2 pair comparisons, two minimal computations and loop overhead fit1024s^7. No caching is assumed.

These allowances use at most8 scalar operations per traversed/copied list or address cell plus bounded constructor/field/control overhead, as in the corrected prior contract. Every rooted-span/minimal output names an original subtree vertex, so list length and address length are at most N; prefixing opposite children preserves vertex distinctness. A block is at most M long, and n,p<=s. The guard table plus extra P.length/budget/head/setup operations fits256s^3+1024s^7+32s+64, below4096s^8 for s>=3. This includes fixed wrapper work rather than interpreting the formal head charge1 as every separately counted match/constructor. The guard bound is a conservative source inspection argument, not an extracted operational semantics theorem.

For blockColor a lookup scans visited blocks, performs contains on their labels and stops at the unique containing block's head. A conservative independent sheet is8M+16p+8 per lookup: membership cells cost at most8, each visited block's control/base costs at most16, and head/return setup fits8. This is at most32(M+p+1). The actual core fromTree calls color once at every original leaf after its own Nodup guard, so C=32n(M+p+1) pays all finite color computation. FinalWork.meterColor:28 uses the same contains branch and returns the same value, but its full-block work field is nominal meter arithmetic, not a fine-operation identity. The coarser C also covers its proven upper envelope. No arbitrary color oracle remains in this recovery wrapper. Scalar color values are original P representative labels and, on accepted input, have at most the source-label width.

Actual finite readouts check all admitted label/color values and total nominal color work<=C, while the frozen reference records every block inspection, membership comparison and first-head access. Those reference counts are not renamed as extracted candidate counts. The separately traced generator makes n color invocations on accepted fixtures and none under the recovery guard on refused fixtures. Input rank is computed only as a diagnostic in the reviewer adapter and as a mathematical proof term in the package; it adds no production recovery call.

## Full source generation and composition

The prior corrected source contract gives the whole generator envelope

    I+(A+6)(B+1)2^(B+1),
    I=128(N+1)^3, A=256((N+1)(N+2))^3, B=min(k,n-1).

This pays initialization/fromTree/Nodup again, all evaluated local prefixes, both attempted branches, root/duplicate/erase refusal work, zero-budget local work and pruned continuations, output construction, counters and actual receipt-list append materialization. Correct copying uses8 operations per copied outer cell, not the formal meter's one-cell unit. The corrected recurrence retains exactly the same displayed closed envelope because the local cap is large enough. No singleton-output observation deletes failed/pruned prefixes or resets their work. Previous source correspondence is reused explicitly, not re-counted as a fresh proof.

On accepted input, FinalWork.checked_flatten_perm:83 proves M=n, blocks_le_flatten proves p<=n, and checked_rank/inputRank_pos prove p>=1. Thus B=k=p-1. With all wrapper guard/setup/color costs above, the source bound is

    Wsource <= G+C+I+1+(A+6)p2^(k+1)
            <= [G+C+I+1+2(A+6)p]2^k = F(S,P)2^k.

FinalWork.final_work_bound:116 checks the analogous algebra for the formal meter; it is not the proof that each formal intermediate work field upper-bounds actual fine work pointwise. The separate inspection and corrected generator envelope give the same final formula. G has degree8 in n, C degree2, I degree3 and2(A+6)p degree7 on accepted input, so F=O((n+1)^8). The returned original cut count is exactly k, allowing the exponent substitution at FinalWork.final_work_actual_cost:143.

Source-only success does not itself imply the final P is an AF with the target or is minimum. Recovery works for any checked P. Only the future main call supplies original agreement, final selection and k<=q. For rational c>=2 and k<=q,2^k<=c^q, so ONE final bill fits F*c^q; FinalWork.final_work_absorbed:165 proves that rational arithmetic. The kernel does not enforce the main caller's invocation multiplicity. Eight repeated calls at k=q=3 have charged exponential factor64 versus8 for one call, as both the frozen arithmetic controls and explicit false proposition demonstrate. This rejects deleting multiplicity from the sum of per-call charges. It is not a tight runtime lower bound or a claim that the generous single-call F bound must fail at that particular tiny fixture. No per-branch recovery discount or cost for finding P is accepted.

## Encoding and limits

For accepted input let L be one plus maximum original-label bit length. All P labels/representatives are original labels, k<=n-1, and core counters are bounded by all-prefix counts of O(2^n), hence require O(n) bits. Address lengths are at most N. Under direct binary comparison/addition/subtraction and the stated reference/list representation, multiply structural source work by O(L+n+1), and add input encoding length. The accepted-input bound is

    O((L+n+1)(n+1)^8 2^k + input_encoding_length).

For REJECTED arbitrary input the structural G uses N,M,p; the bit factor must also include every supplied P label, including absent huge labels. The accepted n-only/L-original simplification is not claimed for malformed P. The huge-label fixture retains129-bit labels AND representatives. No word-overflow truncation or constant bit-cost premise is introduced.

Output values share immutable references. Serializing the one returned certificate adds n original labels and k addresses of at most N bits each; this is an additional polynomial term covered by the generous guard/source envelope under the stated encoding. The semantic proof's full original components are not secretly materialized or serialized by recover. No external target query or hidden oracle is included. Empirical build/readout timings describe only their local configurations. Machine instruction/cycle/verified compiler/GC bounds, the main minimum selector and global recurrence remain OPEN. A later fresh-context prose/referee pass is pending root assignment.
