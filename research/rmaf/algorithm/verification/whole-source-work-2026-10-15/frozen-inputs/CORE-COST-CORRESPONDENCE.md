# Independent source-cost correspondence

The displayed standalone bound survives under the explicit ordinary list/address contracts below. The exact identification of the author's helper units and metered recurrence with every primitive operation in its prose convention does not survive. The repaired correspondence here is a mathematical inspection argument with separately checked arithmetic; it is not an extracted compiler trace.

This is the same reviewer lineage, with zero added independent replications. The 29 clean/61 corrupt readiness cases predate candidate contact. The comparison adapter uses only the frozen independent `work_ledger.py`, plus source-bound calls to the separately rebuilt candidate. The supplemental unit witness is explicitly post-candidate.

## Source sites and numerical witness

`isolated/CoreProgram.lean:21–27` constructs each original address by a left append and invokes color once at each original leaf. `:29–46` performs recursive normalization and erasure; `:48–74` includes both possible pure `mixedCherry` arguments, all/find/filter/length and color tests. `:91–106` contains both receipt-list appends, root/duplicate/entire refusal guards and successful callback updates. `:108–126` includes a second group traversal, current payload flattening, detached outer map/append, zero-budget local work, initial leaves/Nodup and accepted-branch cap/conversion.

On a full left comb with eight groups, the frozen independent ledger observes 15 `groups` node visits, seven append calls and 28 copied left cells. There are eight singleton group constructors. Merely counting tree matches, singleton cons, append match+cons per copied cell and append bases gives `15+8+2*28+7=86`. The actual helper `Primitive.lean:19–21` returns `8*2+7*5+28=79`. `SOURCE-UNIT-WITNESS.json` and the clean/explicit-false Lean controls retain this discrepancy. Thus the claim that this helper itself covers every separately listed match/constructor unit is REFUTED-AT-WITNESS. This does not refute its much larger table bound or the final cap.

Likewise `Work.lean:119` counts one unit per left output/refusal cell, and `:149–153` adds that once at a receipt join. A literal copy needs more than one separately counted primitive operation. Its formal `envelope` is a theorem about that meter, not an exact source instruction trace. The corrected recurrence below includes a conservative cell multiplier.

## Explicit upper contracts

Use ordinary recursive immutable lists. A copied cell costs at most eight scalar source operations, including its match, reference moves and constructor; empty append bases have fixed overhead. An inspected Boolean-address bit costs at most eight operations plus fixed list bases. List predicates charge scalar Nat comparisons separately. Tree-node fixed allowances include constructor/match/field/control operations. Nested group labels and output objects are shared references when an outer list is copied. This is a declared source model, not a machine-cycle or exact Lean Std implementation certification.

The installed Lean4.35.0 `Init/Data/List/Basic.lean:1381–1403` implements Nodup by tail-first Pairwise and a bounded all scan (`:877–892`), giving at most n(n−1)/2 label comparisons. Its comparison order differs from the reference ledger, which never claimed exact Std equality. The same file defines filter/find/all at :483–489/:1609–1614/:1918–1921. Its compiler substitution for append uses two reverse passes (:593–607), further reason not to identify copied cells with one actual instruction. `RUNTIME-LIBRARY-CONTACTS.json` pins these contacts. The proof below uses source/library upper contracts, not compiler replacement timing.

Write s for incoming current footprint, a for detached group count, b for cut count. The independent conservative local sheet is:

| site | upper source charge |
|---|---:|
| normalize | `(s+24)s` |
| initial groups | `(s+16)s` |
| all | `8s+4` |
| find/filter/result length | `(16s+24)s+4` |
| eager mixed traversal/result test | `16s+24` |
| each of two attempted children | `(b+1)(8s+24)+(8s+24)s+32` |
| finish groups/flatten/map/outer append | `(s+16)s+24(s+a+1)` |
| dispatch, receipt bases, counters and fixed control | `96` |

Both attempted children and finish are included even though a step uses only one branch. Guards and early erasure reduce work. Pruning occurs after this local bill.

For normalization let i be current internal nodes and P current stored label cells. Footprint has `s>=2i+1+P`. Total left payload cells copied during all homogeneous contractions are at most iP: each original stored cell is copied at at most i ancestors. Eight operations per such cell fit the leading square because `8iP <= (2i+P)^2 <= s^2`. Fixed 24 per node covers the remaining operations. For groups, left copied cells are at most `i(i+1)/2`, by induction on the internal-node split (the difference at a split a,b is b(a+1)). Thus eight operations per copied cell are at most `4i(i+1)<(2i+1)^2<=s^2`; fixed 16 per node covers the rest.

All scans at most s groups. Each find candidate scans at most s group cells, allocates at most s filter cells and traverses at most s result-length cells; 16s+24 per candidate is conservative. Mixed traversal uses at most the current tree's nodes, including both pure arguments of Option.or. A selected group is in `groups(normalize current)` by `Payload.selected_mem:12` and the frozen chooser occurrence lemmas in `Branches.lean:60–84,175–208`; its origin length is at most s by `Work.group_size:64`. Cut membership scans at most b comparisons, each stopping after at most the selected-origin length plus its base, even if an arbitrary stored cut address is longer. Erase traverses at most s nodes and compares original addresses of length at most s. Its option/suppression constructions fit the stated constants. Finish copies at most s current label cells, maps/appends a outer detached cells and shares inner labels. No unbounded nested detached copy is charged as a scalar.

Let R=s+a+b+1. The sum is at most `567R^2`. For actual standalone calls, `Within` and its literal continuation preservation (`Work.lean:246–263`) give R<=M=m+1, where initial m=N(N+2)+N+1. Nonempty Tree gives N>=1, m>=5 and M>=6. Therefore `567R^2 <=567M^2 <=256M^3=cap m`. This only needs the actual generator's resource range; it makes no source-cost assertion for arbitrary malformed metered callbacks. `ReviewCostBridgeV4.lean:8,33` checks the arithmetic, with only propext and Quot.sound. The source-site correspondence remains this explicit inspection argument.

## Receipt materialization and initialization

`Work.run_records_events:219` bounds record count by visited+attempts and `run_records_bound:239` gives `3*2^(j+1)` for a returned budget-j subtree. Duplicates and refusal records remain records. At budget zero there can be two pruned callbacks and one left refusal record; at larger budgets, the whole left returned record list may be exponential. With L=cap m, the conservative source recurrence is

    F(0,L)=L+10
    F(j+1,L)=L+2F(j,L)+24*2^(j+1).

The factor24 is eight operations per copied cell times the three-times-power record envelope. Empty append bases and fixed receipt operations are in the local charge. Two pruned callback constructions are allowed by the ten. For L>=12, this satisfies the SAME closed bound `(L+6)(j+1)2^(j+1)`: with p=2^(j+1)>=1, the induction tail uses `L+24p <=2(L+6)p`. `ReviewCostBridgeV4.lean:47–66` checks this arithmetic. L is at least256 on the used resources. The retained j+1 factor charges repeated copying; prefix count alone would be inadequate.

A conservative initialization tally excluding oracle evaluation is `22N^2+80N+16`: two leaves builds use at most `8N^2+32N`; the quadratic Nodup scan at most `6N^2+16N`; original-address conversion at most `8N^2+24N`; accepted length/cap and refused construction at most `8N+16`. This permits both leaf builds, all address left appends, tree constructors, comparisons and fixed control. It is bounded by `128(N+1)^3` (`ReviewCostBridgeV4.lean:68`). The formula therefore remains

    128(N+1)^3+(256((N+1)(N+2))^3+6)(B+1)2^(B+1),
    N=2n−1, B=min(q,n−1).

The source conversion makes n color invocations on accepted labels and zero on duplicate refusal. Arbitrary color evaluation costs must be added. Finite comparisons reproduced those calls, both receipt-copy lists and actual prune calls; they did not establish the general bound by sampling.

## Runtime interpretation and boundary

The formula gives O((n+1)^7 2^B) structural source operations: the cap is degree six in n and B+1<=n. Scalar Nat operations cost one here. With binary labels/colors/budget/counters, retain H as one plus the maximum relevant bit width, including supplied q even when clipped and B+O(1) counter widths. Under direct scalar implementations, multiply by O(H), add input encoding length and the sum of actual color-evaluation costs. A finite color table has its own construction and lookup bill. The returned color's size does not bound an arbitrary function's evaluation time.

Materialized output lists share nested objects. A serializer that writes every nested output afresh must additionally traverse its O((B+1)S) label/address payload per output; this remains polynomial-times-2^B under the same bit representation. A word RAM interpretation assumes words/references accommodate stored scalars and memory addresses and that the primitive/list implementation meets these contracts. Machine instruction counts, cycle bounds and a verified compiler/GC cost theorem remain OPEN.

No actual ownership-prefix caller, weighted sum, pair/refinement composition, residual original-component realization or finite-budget output coverage is proved here. These are named obligations, not assumptions discharged by the cost meter. All three main milestones remain OPEN.
