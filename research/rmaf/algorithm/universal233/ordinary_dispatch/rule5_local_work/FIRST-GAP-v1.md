# Exact first missing Rule5 local-work call

Functional and actual trace correctness were already sealed. This is a local
body-cost gap, not a geometry or AF correctness gap.

Hard2Dispatcher.rule5Answer -> Rule5OrdinaryDispatch.dispatch ->
Rule5FinalClassification.selectFinal -> Rule5Classification.selectLocal ->
Rule5Local.admitted T S a b is the first unmetered source call in evaluation
order. Its first properPair T S guard already requires actual leaf-list/nodup/
contains scan correspondence; later guards scan candidates, cuts, original
source embeddings and restrictions. The frozen Rule5Defs.lean body is used,
not a replacement guard or SourceIH. Its functional admitted hypotheses remain
proved by the earlier seals. No whole-body work theorem has been assumed here.

After this first call, the remaining unmetered calls include selectLarge,
selectSizeTwo, selectOutside, badCandidates/selectBad, selectBoundary and actual
selected children/materialization; common buildSetup and outsideReply pretests;
paid.second buildSelected geometry enumeration, requests and currentFrontier;
and ordinary child source-state checks. The old source-count helpers do not
establish their full body/bit bills. These are not discharged by this stage.

This stage closes a concrete later source body: actual common owner-pair
mergeCandidates -> checked best -> reconstruct, with proved actual closed
callback payload and numeric domains. Agreement-checker and scalar primitive
correspondence is explicitly open at PRIMITIVE-INTERFACE-v1.md.

No complete Rule5 local-work polynomial, full source/bit recurrence, fast base,
main milestone, independent acceptance or novelty claim follows from this stage.
