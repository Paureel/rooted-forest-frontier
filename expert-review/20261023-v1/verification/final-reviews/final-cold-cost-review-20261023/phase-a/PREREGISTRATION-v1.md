# Frozen before execution or candidate contact

Author: the assigned cold operational-cost agent; date 2026-10-23. This is own synthetic calibration, not an implementation or theorem about the unreleased candidate. No project verifier, author result, peer report, control, or oracle is reused. The only target is the screened TARGET-v3 question in the v1-named target file.

## Primitive instrument

For unsigned integer `x`, `b(x)=max(1, bit_length(x))`. A primitive event with ordered operand tuple `u` costs `1 + sum(b(x) for x in u)`, retaining operand multiplicity. The synthetic interpreter records every ALLOC, READ, PRODUCE and DECIDE it actually performs. ALLOC owns the initialized cell and includes both its address and value as operands; READ includes address and returned value. A cell remains retained forever. ALLOC is a declared toy primitive, not a theorem about a real allocator or Python internals. One synthetic MUL includes both argument occurrences and its result.

No claim is made that the toy fee schedule is the candidate fee schedule. Later mapping must start from the released exact computational routines and fee TYPES. The instrument calibrates occurrence accounting, arithmetic, inequalities and dependency alarms; it cannot prove missing operational coverage by itself.

## Positive controls and independently constructed expectations

P0: no event and no allocation gives bill 0, cells 0, address-bit fees 0, events 0, maximum-address width 1 (the null-address convention).

P1: initialize two source cells, values 7 and 9, at addresses 1 and 2. Eagerly generate occurrences 1, 2 and 3. Each PRODUCE has the occurrence ID as its sole operand. Each occurrence reads both source cells and ALLOCs fresh copies, then ALLOCs its occurrence ID in a metadata cell. Thus copies for occurrences 1/2/3 have addresses (3,4)/(6,7)/(9,10), and metadata has addresses 5/8/11. All three payload lists equal [7,9]. Judge stored occurrences in dynamic order 3,1,2; read the metadata and DECIDE(id,flag), with flag 1 only for occurrence 1. Later refusal never deletes earlier eager work.

The manual fee ledger is: initialization 12; producer 8; copy READ+ALLOC 82; metadata ALLOC+READ 38; decisions 11; complete bill 151. There are 26 events, 11 retained cells (2 source, 6 copied, 3 metadata), 3 produced/visited occurrences, 1 distinct payload, 1 accepted occurrence and 2 refusals. Eager generator work owned by refused occurrences is 37+39=76, already included in bill 151. Allocation address-bit fees sum to 33; source READ address-bit fees sum to 9; metadata READ address-bit fees sum to 11; total address-bit fees 53. A structural allocation bound comes first: `2+3*(2+1)=11`. Therefore maximum allocated address width is 4. With at most two operands per event and each width at most 4, the coarse independent fee bound is `26*(1+2*4)=234`, and `151<=234`. Retained cell count 11, address width 4 and aggregate address-bit fees 53 are different quantities.

P2: `MUL(8,8,64)` costs `1+4+4+7=16`; deduplicating repeated operands would incorrectly give `1+4+7=12`.

P3: dependency graph `allocation -> inputs`, `width -> allocation`, `operand -> inputs`, `fee -> {width,operand}`, `desired_bill -> fee` is acyclic. It records an admissible direction only; every graph node still needs actual mathematical support after release. A deliberately false allocation dependency on desired_bill creates the exact cycle `allocation, desired_bill, fee, width, allocation` and must be rejected.

P4: a finite optimizer with initialization 2, all trial bills [3,5,7], and exactly one recovery of bill 11 costs 28. Its source mass is the toy integer `M=1+2+3=6`, and `4*(M+1)=28`. Omitting the two failed trial bills would report 20. A second recovery would change the recovery count from 1 to 2 and add 11. These data are synthetic and are not `sourceOptimizeMeter`.

P5: let `r=233/100`, `Q=2`, `k=3`, `P=2`, `A=4`, `M=6`, `C=28`. Exactly `P*r^Q=54289/5000`, so `M<=P*r^Q`; `C=A*(M+1)=28`; monotone substitution yields `A*(P*r^Q+1)=59289/1250`; absorbing the +1 using `r^Q>=1` gives `A*(P+1)*r^Q=162867/2500`; increasing from Q to k gives `37948011/250000`. All inequalities must be checked by exact rational arithmetic, without floats. The intentionally false dropped-+1 bill bound is `28<=24`, residual 4. The false source bound `6<=1*2^2` has residual 2.

## Corrupted twins and exact mandatory diagnostics

All ten must be detected, one at a time, against the clean measured twin. A missing case, wrong diagnostic or wrong expected/observed value is a failed calibration. The negative child exits 23 only after all ten exact catches; unexpected survival or mismatch exits 1. The positive child exits 0 only after all six positive cases match. The known output is read semantically, not inferred from the wrapper status.

| ID | Deliberate corruption | Required diagnostic, expected, observed |
|---|---|---|
| N1 | collapse equal payload copies | DUPLICATE_COPY_UNDERCOUNT, 6, 2 |
| N2 | remove eager generator fees of later-refused occurrences | EAGER_REFUSED_WORK_OMITTED, 151, 75 |
| N3 | omit retained metadata allocation count | METADATA_ALLOCATION_OMITTED, 3, 0 |
| N4 | replace retained cells by address width | RETAINED_CELLS_CONFUSED_WITH_WIDTH, 11, 4 |
| N5 | deduplicate repeated arithmetic operand | ARITHMETIC_OPERAND_MULTIPLICITY, 16, 12 |
| N6 | infer allocation through desired bill | CIRCULAR_WIDTH_DEPENDENCY, acyclic, allocation/desired_bill/fee/width/allocation |
| N7 | omit failed optimizer trials | OPTIMIZER_FAILED_TRIALS_OMITTED, 28, 20 |
| N8 | count a second recovery | RECOVERY_MULTIPLICITY, 1, 2 |
| N9 | drop the source-mass +1 in bill bound | INEQUALITY_FALSE, lhs 28, rhs 24, residual 4 |
| N10 | claim false source exponential bound | SOURCE_BOUND_FALSE, lhs 6, rhs 4, residual 2 |

## Execution, timing, and failure policy

Two bounded children only: `controls-v1.py positive` then `controls-v1.py corrupted`. Run both with `./bootloops-python`, through the existing unchanged run_capped.py, omit --seconds to retain default 30, and use the wrapper's shared `.runtime/rmaf-proof-compute.lock`. The corrupted child uses --want 23. Finite work is 26 toy trace events, one MUL, two tiny DAG traversals, and fixed rational expressions: no unbounded search or scaling projection. Runtime is unknown before measurement. Semantic progress is six matched positive cases and ten caught named corruptions in retained JSON output. No cap raise or unchanged passed rerun is permitted.

If a control fails, retain all original bytes, output and diagnostics and add a prospective v2 erratum before a new run; never edit/rescore v1. Shared Python integer/Fraction implementation, wrapper and pinned supervisor remain common infrastructure and cannot supply independent mathematical/kernel credit. No candidate verdict is licensed. Seal report, preregistration, script, outputs and receipts, then stop for an explicit screened computation/full TYPE release.
