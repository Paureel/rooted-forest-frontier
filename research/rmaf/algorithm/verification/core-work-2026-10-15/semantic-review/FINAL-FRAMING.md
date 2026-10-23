# Final core-work framing pass

One narrow correction is required before sealing. The four final documents
otherwise keep the accepted source envelope, rejected operation-unit
identification and open machine/global obligations distinct.

## Read scope

This pass read only the final RESULT.md, COST-CORRESPONDENCE.md,
CONSUMER-TRACE.md and FINAL-RECEIPT.json immediately above this directory.
It performed no computation, replay, source/library inspection or new
independent verification. Numerical and kernel evidence reported by those
documents remains the parent's evidence; this pass checks its framing.
The earlier semantic review's zero added replication count is unchanged.

## Required correction

FINAL-RECEIPT.json:149–151 marks extracted compiler/machine runtime OPEN,
then describes its obligation as a verified correspondence "or measured
machine-bound claim". That alternative can imply that timings discharge
the general runtime correspondence. Empirical measurements justify only
their measured configurations and cannot supply that general bound.

Replace the obligation text with:

> Verified source/library/compiler/allocation/GC cost correspondence for a
> general runtime bound; empirical timing would support only the measured
> configuration and is not furnished here.

This is a claim-boundary correction. The existing OPEN verdict stays in place.
No computation or additional research is required to make the correction.

## Claim-strength checks

| boundary | final evidence location | framing finding |
|---|---|---|
| source acceptance is conditional on primitive contracts and corrected domination | RESULT.md:3,15,23,30; COST-CORRESPONDENCE.md:3,17,40; FINAL-RECEIPT.json:129–146 | clear |
| exact helper identification fails at a concrete operation-unit witness | RESULT.md:14,21; COST-CORRESPONDENCE.md:11–13; FINAL-RECEIPT.json:115–126 | clear: 79 helper units versus minimum 86 separately counted matches/constructors, not machine timing |
| formal meter theorem does not by itself certify source work | RESULT.md:21–23; CONSUMER-TRACE.md:14,18–20; FINAL-RECEIPT.json:137 | clear |
| source inspection and arithmetic have different evidence | COST-CORRESPONDENCE.md:36–40,49–51; RESULT.md:23 | clear: source correspondence remains mathematical inspection; the additional Lean bridge checks arithmetic |
| returned records, failed/pruned attempts and repeated materialized joins remain charged | COST-CORRESPONDENCE.md:34,44–49; CONSUMER-TRACE.md:14–18 | clear: eight-operation cell factor and depth term retained |
| initialization, arbitrary color evaluation, oversized Nat inputs and serialization are scoped | RESULT.md:30; COST-CORRESPONDENCE.md:51,56,60–62; CONSUMER-TRACE.md:8 | clear |
| machine/compiler runtime stays open | RESULT.md:17,30; COST-CORRESPONDENCE.md:62; FINAL-RECEIPT.json:149–151 | clear OPEN verdict; correct the empirical-timing alternative above |
| actual ownership construction/summation, pair composition, original realization and coverage stay open | RESULT.md:18–19,40; COST-CORRESPONDENCE.md:64; CONSUMER-TRACE.md:23–25; FINAL-RECEIPT.json:153–169 | clear; all three main milestones OPEN |
| lineage, post-candidate witness and child contact do not become extra replications | RESULT.md:7; COST-CORRESPONDENCE.md:5; FINAL-RECEIPT.json:4–5,171 | clear |
| novelty is not inferred from local proof or replay | RESULT.md:40; CONSUMER-TRACE.md:25; FINAL-RECEIPT.json:170 | clear; no novelty assessment performed |

No other substantive source/kernel/machine/global claim-strength correction
was found in these four documents. This pass does not re-audit the counts or
independently certify library locators reported in COST-CORRESPONDENCE.md:19.
After the single receipt correction above, the framing supports the parent's
scoped verdict while all three main milestones remain OPEN.
