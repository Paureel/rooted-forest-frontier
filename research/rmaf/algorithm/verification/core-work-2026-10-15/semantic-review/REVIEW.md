# Frozen core-work semantic review

The displayed standalone source-envelope bound can survive a more conservative
operation count. The frozen author meter is not itself an exact charge for every
operation in the convention stated in COST-MODEL.md. Acceptance therefore needs
the reviewer's separate domination proof and an explicit correction to that
identification. This review does not certify machine instructions, audit Lean
axioms, or close any of the three main algorithm milestones.

## Scope and contacts

The review read only the permitted isolated Work.lean, Primitive.lean,
Payload.lean and CoreProgram.lean, the author's COST-MODEL.md and RESULT.md,
and the preregistered OPERATION-SPEC.md. No author replay, other verifier
implementation, live assembly, whole-source mass/work consumer, pair proof or
other completion review was read or executed. The parent supplied a proposed
conservative local sheet before this review assessed it. That contact is part
of the provenance; this is a semantic review, adding zero independent numerical
replications. No child was spawned and no kernel/computation replay was run.

The source hashes recorded by a local SHA-256 command were:

| source | SHA-256 |
|---|---|
| isolated/Work.lean | 99a5cfadd532db40b66a07bb0d3ec673aba49fe9455db2998100d64d10f39e56 |
| isolated/Primitive.lean | d51ec551a3eade2ef1f08409eb97f047752ab77393e5a8be11346dc2c41ad405 |
| isolated/Payload.lean | 45c009c0d2a1d1e5c01fe2ab664819b95a0f733dfe9bed6df4ed73f241eede19 |
| isolated/CoreProgram.lean | 9aa92355dfecf6e0e3d7707c1c284cabcb2f3846b6682e3b55b719e35cb7311f |
| author COST-MODEL.md | bce2a75649757a260cb0f5a12a5f458cc73dfc5584792887a8f411029c38022b |
| author RESULT.md | 4c49b7253e1532a99d3f46087ddc4fc7a3649ad31d291903bc1a8016af46be9c |
| preregistered OPERATION-SPEC.md | ba2763b78969e7ca7a79b248c204e69de1776fae1d0bf4b82ea4a682a69a5b06 |

## Read facts and findings

1. **The source convention and exact helper charges differ.** COST-MODEL.md:13
   says a list constructor and match "each cost one source operation"; :15
   says the helper constants cover these operations. Primitive.lean:19–21
   assigns one unit per left group-list cell at append, in addition to a fixed
   five per internal node. On a full left comb with eight leaf groups,
   `groupsWork = 8*2 + 7*5 + (1+...+7) = 79`. Even counting only the literal
   tree matches, singleton constructors, append matches, append constructors
   and append base matches gives `15+8+28+28+7=86`. These are hand-derived
   arithmetic counts, not an executed trace. They refute the claim that this
   exact helper charge is an upper count in the stated separate-match-and-cons
   units. They do not refute the much larger table bound `(s+5)s`.

2. **The same distinction matters globally for receipt append.** Work.lean:118–119
   defines `appendCells` as the left output/refusal record count. :149–153 adds
   that quantity once to metered work. CoreProgram.lean:91–93 contains two
   literal list appends. One copied spine cell entails a match and a constructor
   under the written convention, with further reference operations depending
   on the explicit primitive contract. COST-MODEL.md:66–71 calls its recurrence
   "the honest recurrence" for source work; as an exact identification with
   those units, that wording needs correction. A fixed local allowance alone
   cannot substitute for a per-cell factor on an unbounded returned receipt.

3. **The source sites needed for a conservative rescue are present.** The
   source performs normalization before choosing (CoreProgram.lean:108–116),
   checks root/duplicate cuts and erases before invoking the continuation
   (:97–106), and invokes that whole step at budget zero (:120–122). Therefore
   the pruning callback cannot erase the preceding local bill. Work.lean:138–158
   charges the local envelope at every step and separately charges successful
   pruned callbacks. Its `prunedCalls` equality at :182–201 is a count identity;
   it is not a proof that the local source bill vanished. The source performs
   a second group traversal and flattening at finish, and maps/appends the
   detached outer partition list (:112); a source sheet must include all of it.

4. **Detached data and oracle scope are not silently scalarized.** Payload.lean:28–39
   defines literal successful prefixes and states separate current, detached
   and address-volume bounds. :64–72 includes the last attempted child under
   the supplied depth condition. Deriving that depth condition for actual run
   calls is the ordinary source recursion argument, not a conclusion of the
   numerical resource invariant alone. Work.lean:375–392 and :422–426 expose
   the syntactic color call count; CoreProgram.lean:124–126 checks Nodup before
   conversion. An accepted input has one source invocation per leaf; refusal
   has none. The arbitrary function's evaluation bill remains external.

## Checked mathematical rescue

The following is a source-envelope argument under declared simple immutable
list/Boolean-address contracts, rather than a claim about Lean Std internals.
The parent supplied the local sheet; this review checked its structural
justification and the global recurrence algebra. The parent's separate Lean
domination proof was not read or replayed here.

Write `i` for current internal nodes and `P` for current label-list cells.
The current footprint satisfies `s >= 2i+1+P`. The total number C of label
cells copied by all homogeneous appends during one normalization is at most
`iP`: every original stored label cell can be in at most i copied left payloads.
In particular `3C <= 3iP <= (2i+P)^2 <= s^2`. Even eight operations per copied
cell fit the leading square, since `8iP <= (2i+P)^2` follows from
`(2i-P)^2 >= 0`. This supplies a reason for a leading `s^2` term that does not
come from identifying `normalizeWork` with a literal operation trace.

For group-list copying, the maximum left-spine sum on a full binary tree with
i internal nodes is `i(i+1)/2`, attained by the full left comb. An induction
uses the internal-node split: the sum of the two child maxima plus the left
leaf count is bounded by the parent maximum. Thus even eight operations per
copied group cell satisfy `8C <= 4i(i+1) < (2i+1)^2 <= s^2`. Fixed costs per
node can then be covered separately. These observations justify replacing the
exact helper-identification claim with a genuinely conservative local sheet.

The final recommendation uses the parent's subsequently supplied larger
eight-operation sheet: normalization `(s+24)s`, groups `(s+16)s`, all `8s+4`,
find/filter/length `(16s+24)s+4`, mixed traversal `16s+24`, two guarded erasures
`2*((b+1)(8s+24)+(8s+24)s+32)`, finish `(s+16)s+24(s+a+1)`, and fixed 96.
The contracts are simple recursive immutable lists with at most eight
operations per copied cell; address comparison uses at most eight per
inspected bit plus its fixed base; Nat scalar operations remain unit source
operations at this stage. These are upper contracts, not byte-for-byte
instruction counts for a chosen Lean runtime.

Normalization and group-copy costs fit the squares by the bounds above, with
24 and 16 fixed operations per tree node respectively. All gets eight per
candidate plus four for its base. For each find candidate, filter can spend
eight operations per scanned cell for match, color fields/test and conditional
allocation, and another four per retained cell on result length; 16s plus
24 fixed operations therefore leaves room. Mixed traversal's 16 per node and
24 final operations include both pure arguments of Option.or and the final
result/color test. The guard and erase rows allow eight per address bit plus
24 for the list/option bases, guards, constructors and suppression cases.
The child allowance 32 and fixed 96 cover cons/update/refusal and remaining
dispatch/counter fields. Finish's extra `24(s+a+1)` covers flatMap label
copies, detached map and outer append; inner detached label lists are shared.
No unit-time deep detached copy is used.

With `R=s+a+b+1`, a coarse domination by `567R^2` is sufficient (and roomy).
For the standalone generator let `M=m+1`, where
`m=inputResource=N^2+3N+1`. Work.lean:245–263 and :428–437 preserve `R<=M`
for evaluated calls. Nonempty input gives `N>=1`, hence `m>=5` and `M>=6`.
Thus `567R^2 <= 567M^2 <= 256M^3`, preserving the displayed local cap.
This argument concerns actual standalone calls; it need not claim a source
simulation for all arbitrary numerical resource parameters. The source
correspondence remains conditional on the explicit ordinary list/address
contracts; the frozen helper definitions do not prove it automatically.

For returned receipt copying, let L bound the conservative local source charge,
including empty-append bases and fixed receipt construction. With at most
eight source operations per copied receipt cell, use

    F(0,L) = L+10
    F(j+1,L) = L+2F(j,L)+24*2^(j+1).

The ten allow two pruned callbacks and eight operations for the possible left
refusal cell at budget zero. The larger-budget term uses eight times the
`3*2^(j+1)` record bound. Setting `p=2^(j+1) >= 1`, the induction to the
unchanged closed bound `(L+6)(j+1)2^(j+1)` needs
`L+24p <= 2(L+6)p`. Its slack `(2p-1)L-12p` is nonnegative for `L>=12`:
it is at least `12(p-1)`. The base follows from `L+10 <= 2L+12`.
The actual cap is far larger than 12. Thus the final formula need not change
merely because its exact append-unit recurrence needs correction, and the
repeated-copy depth factor remains charged.

Initialization has ample room under a direct quadratic Nodup/list contract.
For example, with up to eight operations per copied list cell, fixed per-node
allowances and twelve per Nodup tested pair, a conservative non-oracle tally
is `22N^2+80N+16`: two leaves builds at most `8N^2+32N`, Nodup at most
`6N^2+16N`, original-address conversion at most `8N^2+24N`, and length/cap/
refusal at most `8N+16`. Each tree is nonempty, so `N>=1`, and this sum is
less than `128(N+1)^3`. This is a sufficient algorithmic contract, not an
inspection of Lean's selected Decidable/List library implementation;
OPERATION-SPEC.md:70–72 already requires that distinction.

## Framing audit

| audience | strongest standard objection | axis | answer / correction | severity |
|---|---|---|---|---|
| formal verification | Does the kernel prove source cost, or the bound on a hand-assigned meter? | correctness | Work.lean proves the latter; preserve the separate proof-by-inspection boundary and the conservative reviewer domination. Correct the exact helper/recurrence identification above. | HIGH until corrected in the review verdict |
| complexity theory | Does the bill include large joins, failed children and zero-budget work? | correctness | CoreProgram.lean:91–122 and the corrected recurrence above account for them; a prefix count alone would not. | addressed with amended recurrence |
| implementer | Does this promise CPU/Lean-compiled time, polynomial arbitrary colors, or hidden fixed-width Nats? | correctness | COST-MODEL.md:79–87 exposes the RAM/bit/oracle assumptions. Keep primitive-library contracts and input encoding explicit. | addressed within source model |
| rooted-MAF consumer | Does one generator bound complete the faster algorithm? | correctness | COST-MODEL.md:89–91 and RESULT.md:23 leave ownership-prefix construction/summation and pair/refinement composition open. All three milestones remain OPEN. | addressed at headline and end |
| all claimed audiences | Is this a new complete algorithm or a literature novelty result? | novelty | Neither source claims that; this review makes no novelty assessment and supplies no literature evidence. | outside scope |

The headline qualification is necessary: a source-envelope bound can be
accepted after the reviewer supplies the corrected domination, while the
author meter-to-source identification remains inaccurate. No theorem-count,
receipt equality or successful compilation by itself resolves that issue.

## Review verdict

**SUPPORTS-SCOPED, subject to the parent retaining the explicit conservative
domination and corrected receipt recurrence.** The source sites, pruning and
materialization accounting support a standalone polynomial-times-2^B
source envelope under the declared primitive contracts. The displayed final
formula is algebraically compatible with conservative per-cell factors.
The recommended acceptance route uses the larger eight-operation local sheet
and receipt recurrence above. The exact author helper/recurrence-to-source
identification is not accepted.
Kernel audit and control execution belong to the parent's separate evidence;
this receipt does not report them as executed. All three main milestones
remain OPEN.
