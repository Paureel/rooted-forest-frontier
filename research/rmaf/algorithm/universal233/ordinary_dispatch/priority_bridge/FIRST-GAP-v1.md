# Executed first dispatcher gap

AUTHOR DEVELOPMENT. The pending predictions in FIRST-CASE-PIN-v1.md are
preserved unchanged. They passed when disk space was restored. Named stored
proofs are `Controls.actual_first_hard2_case` and
`Controls.actual_first_hard2_admission_gap` in GuardControls.lean.

For the frozen Rule5PreControls.commonT/commonS trees, DepthOne.proper is
true. Actual forward CherryBranching.select returns hard2 with endpoints
(3,4) and the literal commonC parent/cuts. The reversed selector returns hard2
with endpoints (7,8) and commonD. Both actual Rule4 selectors return none.

For this actual selected (3,4) pair, the target embedding of the literal
pendantPartition is false and the count of good blocks is 1. Consequently
`Rule5Local.admitted commonT commonS 3 4` is false. The same trees have
`Rule5Local.admitted commonT commonS 0 1 = true`.

Thus the missing implication is concrete: proper ordinary inputs, both actual
hard2 selections and both Rule4 refusals do not imply Rule5 admission of the
first forward selected cherry. A dispatcher that uses the existing DFS
hard2 result needs a further selection argument or a different admitted
cherry search before calling the conditional Rule5 consumer. This case does
not establish the general existence of an admitted cherry and does not
refute the completed conditional consumer for (0,1).

The admission reduction is proved exactly: all printed guards except the
literal target embedding and good-block count follow from these actual
selection/refusal inputs, including source embeddings. No full algorithm,
runtime, base case, novelty or independent acceptance follows.
