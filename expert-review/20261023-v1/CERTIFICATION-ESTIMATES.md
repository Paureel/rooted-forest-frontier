# Optional certification: scope and planning estimates

Neither certification campaign has been resumed. These estimates are engineering judgments, not measured proof throughput, success probabilities, promises, or extrapolations from theorem counts/CPU activity. One person-week means approximately forty focused hours of an experienced Lean/program-verification engineer. Agent-assisted calendar time cannot be reliably converted from that unit without a scoped pilot.

| Deliverable | What would actually be completed | Rough effort budget |
|---|---|---|
| End-to-end machine proof of the mathematical implementation | A Lean operational semantics for the exact projected pseudocode; formal actual-execution/guard/occurrence/projection, local operations, scalar/allocation/width and fee proofs; one whole optimizer theorem joining the existing functional and SOURCE results | 6-16 focused person-weeks |
| Certified runnable RAM executable | Complete the numeric solver/forest/selected-branch/optimizer/recovery bodies, freeze a literal listing and output representation, prove raw-entry no-fault simulation and all concrete allocation/frame/return invariants, then transfer functional correctness and the cost bound to that executable | An additional 8-24 focused person-weeks |

The combined planning envelope is roughly 3-9 months for one experienced full-time person. Some leaf routines can overlap, but the final representation, recursive simulation and cost joins cannot be assumed to parallelize. Both ranges can be exceeded if formalizing the prose exposes a false invariant, an incomplete primitive realization, or a necessary change to the fixed machine/interface. Multiple fresh agents do not provide a justified calendar-speed multiplier.

## Why these are substantial tasks

The existing formal functional theorem and explicit SOURCE exponential theorem are reusable. The new runtime graph construction/determinism, complete operation charging, scalar catalogue induction and global cost join are mathematical arguments, not one compiled complete theorem. Formalizing them requires replacing every written induction and finite case analysis by checked terms and matching operational definitions exactly. A new execution relation is not by itself the requested proof; its connection to the actual bodies must also be formalized.

The saved numeric candidate is not a nearly complete executable. Its frozen status explicitly reports missing body ports at pc3945 (optimizer/scan/recovery), pc3947 (charged-length component) and pc12258 (terminal receipt/selected-branch completion). The public raw route still stops at inherited ports. Literal fetch transfer, reachable record/stack/frame/continuation safety, branch/forest/recursive caller completion and concrete bill bounds remain obligations. See `verification/OPTIONAL-NUMERIC-STATUS.json`, a narrow extraction with the original candidate hash. No missing port is repaired by the mathematical proof or by copying an equal returned value.

The numerical listing route and the mathematical realization have different representations and entry histories. In particular the mathematical optimizer has the explicitly fixed r8/q0 canonical entry. Reuse across routes needs an exact interface theorem; it is not licensed by similar names. The old malformed-memory failure and control qualifications remain historical failures.

## What the estimates exclude

The executable estimate means a verified RAM program with its specified interpreter/machine semantics and complete value/cost theorem. It does not certify macOS, physical hardware, an arbitrary C compiler, the complete native-code toolchain, or elapsed wall-clock performance. A separately compiled native binary would add a new compiler/runtime trust boundary. An ordinary executable that merely returns tested answers has a much lower standard and is not the certification priced here.

A bounded representative formalization pilot would be needed to narrow the ranges: one real recursive routine with full retained fields, allocation/width proof and instruction-cost transfer, not an easy scalar lemma. No such pilot, new theorem run or numerical implementation work was launched for this estimate. The shortest current action remains outside review of the supplied mathematical proof.
