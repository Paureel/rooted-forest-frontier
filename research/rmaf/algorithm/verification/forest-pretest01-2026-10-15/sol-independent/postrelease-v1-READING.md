# Postrelease reading ledger

All entries refer to released/pinned source, freshly read. Facts retrieved
from source are separated from reviewer inferences and executed checks.

## ForestPretestSemantics.lean (own released package)

Read: found_globally_minimum takes only the actual pretest equality and
concludes literal agrees, cost <= 1, and a minimum against every actual
full-state G. Its proof obtains candidate minimum from found_spec and uses
universal_coverage for any competing G of cost <= 1; costs > 1 are excluded
arithmetically. rejected_lower_bound takes only rejected equality and gives
proper plus universal actual-AF lower bound two. pretest_complete takes an
actual AF and small cost, produces found and global minimum. These statements
do not include an optimum callback or desired-coverage hypothesis.

Inference pending dependencies: the semantic wrapper has the intended
quantifiers. Its load-bearing dependency is universal_coverage; candidate
minimum alone is not being substituted for global minimum. Source and
kernel closure checks remain pending.

## ForestCoverage.lean

Read: universal_coverage assumes only actual agrees and additionalCost <= 1;
it returns candidate membership, ForestPerm, actual agrees and equal cost.
It groups F by unique source ownership (regroup_perm), uses
source_blocks_balance for the prepaid sum and obtains each local partition /
source-hull condition directly from sourceCheck. source_small_complete
reduces length to one or two, then calls DepthOne.source_two_split;
assemble_small retains all other current blocks and uses the sum <= 1 to
allow only one nontrivial source cut. No target-clearance premise appears.
ForestPerm and source_two_split remain load-bearing review sites.

## ForestPermutation.lean

Read: ForestPerm has exactly nil/cons(inner List.Perm)/outer(List.Perm)/
append/trans constructors. No agreement, coverage, minimum or cost field.
length_eq and flatten_perm are structural inductions. agrees_perm separately
proves partition, source-family, suppressed restriction and original target /
source hull invariance; it does not bake those into ForestPerm. This agrees
with the licensed definition capsule. No circular desired-result premise was
found in these read statements/proof steps.

## ForestPretest01.lean

Read: executable definitions exactly match the public capsule: no optimum
callback, only unchanged plus original-edge cuts in one current component,
with every other block retained. best receives original agrees on the whole
candidate. found_spec states candidate minimum only, correctly strengthened
in ForestPretestSemantics. refused_iff is actual result equality iff proper
false, without infeasibility language. candidate_cost_le_one uses list
length and Nat subtraction. No rejected/found conflation was found.

## ForestPretestWork.lean

Read: candidates_count proves exact list length one plus summed current
source edge counts. vertices_leaves / edges_leaves use literal binary-tree
induction; candidate_linear_bound bounds by 1+2 times total source leaves.
These are candidate-count theorems only, with no machine-step/runtime claim.
The exact count includes repeated edge partitions.

## Reconstruction01.lean (fresh canonical scientific copy)

Read: source_two_split assumes source Nodup, literal two-block partition
and original source pairwiseEmbeddings only. Its proof uses the proof-only
checked_source_core with twoColor, derives exactly one source cut using two
distinct output blocks and the stated budget, extracts an actual nonroot
source address, identifies its component with subtreeLabels and then with
one input block via monochromaticity/refinement. The executable pretest
does not call that core. This is a different proof route from the reviewer's
direct hull-separation reasoning; checked_source_core and its hypotheses
remain load-bearing sites, and global source-cut recovery is not inferred.

## GroupCostProof.lean

Read: source_blocks_balance derives sum(local block counts minus one) plus
ss.length = F.length directly from agrees, proper source partition,
unique/refined block ownership and nonempty families. sources_le_blocks
then removes Nat-subtraction truncation. The pretest's use needs neither
target-Q disjointness nor CrossClear; other separate reconstruction theorems
in this file do require CrossClear but are not the consumed balance lemma.

## ValidPartition.lean

Read: checked_source_core's source-only premises are Nodup, actual
partitionCheck, actual pairwiseEmbeddings and block monochromaticity. Its
output includes original RealizedOutput and source-cut budget, with
partitionCheck separately proved from payload and cut realization. It calls
source_core (next dependency), with no desired partition-coverage callback
or target assumption in this theorem statement.

## INTERFACE-v1.md

Read: documented consumer imports ForestPretestSemantics and receives a full
label partition, actual agreement, prepaid cost bound and universal minimum,
or proper plus universal lower bound two, or malformed refusal. It explicitly
keeps parent dispatcher/pool/scheduler/IH integration and source work
separate. The document matches the read theorem signatures. Original global
cut recovery is not included in returned F; restrictions/materialization and
their cost require a separate caller obligation. The excluded live dispatcher
was not inspected, so actual parent adoption remains unassessed.

## Cost.lean: source_core

Read: source_core assumes actual source Nodup, partitionCheck, original
pairwiseEmbeddings and block monochromaticity; it invokes
generate_refinement_coverage and separate realized-cut/monochromatic/budget
facts. No polynomial-work assertion is included. The pretest uses it solely
to prove a source separation edge exists; exponential generation in this
proof route is not an executable call in pretest01. Fresh kernel rebuild and
producer/body audit cover the imported proof closure; the broad production
core is not claimed as a newly independent algorithm result.

## SOURCE-WORK-v1.md

Read only after the independent SOURCE-WORK review was written. The author
document explicitly distinguishes exact count from nonformal polynomial
source reasoning, charges arbitrary-Nat bit lengths and full returned
payload, and declines compiled runtime or parent source-bill assertions.
Its displayed loops and sameShape product-of-root-pairs reasoning agree
with this review's own trace. No formal instruction-count theorem is claimed
there. This document is reviewed framing, not independent timing evidence.
