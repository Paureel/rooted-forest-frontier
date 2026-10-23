# Actual source reading notes

## PendantExclusion.lean (full read)

An actual restriction with rooted HasCherry yields PrunedCherry in the original source: at the endpoint fork each selected side restricts to its endpoint, while ancestors preserve arbitrary siblings above that fork. Proper source labels ensure endpoint uniqueness as the fork is traced. fork_excluded identifies the selected root span with the a,b minimal hull and rejects any selected label below an outgoing child. prunedCherry_excluded transports this down the correct original child and explicitly leaves above-LCA directions unrestricted. original_common_block_excluded obtains the cherry from the actual original agreement's restricted RootedIso and applies these facts; it assumes neither source common-cherry structure nor a caller-provided pendant exclusion.

## Refinement.lean (full read)

For a common endpoint block B, original_common_block_excluded prevents any B label below an outgoing path edge. B's hull contains that edge's original parent by endpoint hull monotonicity. If any other block C crossed the same edge, original label-address prefixes and cut_crossing_path force C's unsuppressed hull through that same parent. Actual source embedding disjointness then forces C=B, a contradiction. This proves every F block has uniform membership in each pendant subtree. The argument uses original hull collision and literal labels, not an agreement cut-set subset condition.

## Endpoint.lean (full read)

actual_cherry_endpoint_alternative derives its checked source partition solely from target-side partition and original embedding checks of the given ordinary agreement. If either target cherry leaf is singleton under actual ownership, partition counts prove its literal [a] or [b] block appears in original F. Otherwise each endpoint block occupies the shared original cherry parent; original embedding disjointness forces the owner block to coincide, yielding actual a,b in one F block. History/reachability/owner assignments are not supplied as caller fields.

## Count.lean (full read)

mixed_occupies derives occupation of the exact original edge child from one leaf inside and one outside its source subtree. mixed_blocks_at_most_one then uses actual original F pairwise hull disjointness: two mixed blocks would both occupy that same child vertex. This justifies T1Split's at-most-one extra block and does not rely on a displayed/suppressed edge or a bound assumed from exchange arithmetic.

## CherryReplacement.lean (full read)

reassignedForest prepends b to actual block A and erases A and singleton[b]. checked partitions establish unique label and source-component ownership and forest Nodup. reassignment_preserves_agreement derives A's source component must be the actual common-cherry component by shared endpoint a; all other blocks omit both endpoints by partition uniqueness. Target and source endpoint-reassignment embedding/topology lemmas apply to actual checked restrictions. The result reconstructs every state checker condition. reassignment_length uses two actual distinct member erasures and one inserted block to prove exact |G|+1=|H|, not merely no-larger. T1Exchange uses precisely those derived ownership, topology and length hypotheses, preserving the paid original cuts separately.

## Descendant.lean (full read)

The original subtree address is traversed literally by treeAt; proper source labels give a true original descendant cluster with the opposite child labels excluded. selected_descendant_iff ties label membership to original address prefix via unique leaf addresses. crossing_occupies proves every block crossing that original descendant edge occupies its original child endpoint in the unsuppressed embedding. descendant_agreed_split transports that source cluster only for a final block whose restricted topology actually agrees, then derives target and source separation of the two split pieces. This is a restriction/isomorphism argument, not a common-cluster assumption about the whole target.

## Executable.lean (full read)

Actual vertices retain unsuppressed original addresses in constructor preorder. pendantOriginal filters every original vertex v, excludes root, requires v.dropLast in the original minimal endpoint hull, and v outside it; it recomputes the hull twice per candidate. subtreeLabels follows original child directions and returns that subtree's actual leaf list. The file contains embedded development controls; they were encountered after exact release and are not used as independent reference values or replacements for frozen controls.

## Equivalence.lean (full read)

OutputState original_to_state obtains checked literal source restrictions and transports each refined F block's topology and pairwise embedding to its actual component. state_to_original derives refinement from actual source membership; local original embeddings return through pairwise_transport. Cross-component F embeddings require the explicitly supplied original SOURCE embeddings of Q and subset hull separation. Target embedding of Q is not assumed. The global original agreement reconstructs both partitions from equal labels, target F embeddings and transported local restriction agreement. This is the actual transport used in both directions by T1Exchange, so no source ownership premise is hidden in state semantics.

## Unordered.lean and Interfaces.lean (full reads)

cuts_swap uses exact pendantOriginal swap equality, and unordered safety/exchange handles both orientations of ActualCherry, swapping singleton alternatives and rewriting the literal partition. No endpoint sorting assumption enters. Interfaces is only an import plus #check list of the local declarations; it stores zero declarations. It does not implement final cut recovery. Final recovery remains the explicitly external main caller described in public INTERFACE, outside this local package's executable code and verified scope.

## T1Boundary.lean (full read)

twoBranches is exactly [singleton-a,pendant], with paid1,1 at t1. The older named conditional exchange contract remains, but actual_t1_target discharges it using actual_t1_pendant_exchange and actual_t1_two_minimum supplies that theorem internally. actual_t1_deterministic_minimum uses only the exact literal pendant child IH and the no-larger replacement. These consumers do not charge the discarded proof split or the common-cherry reassignment; they compare returned original forest sizes. The separate three-child cover is deliberately not advertised as the two-child recurrence.

## Budget.lean (full read)

OriginalWithin is existence of original F at |F|-1<=k; ChildWithin is actual feasible refinement at |F|-|P|<=r. remaining_correct derives paid<=k from the actual paid identity and only then subtracts. pendant_checks and endpoint_checks derive checked P/source embeddings/paid counts from proper original T/S/equal labels/actual cherry. branch_checks covers both terminal orientations and pendant. actual_high_budget and actual_t1_two_budget compose those checked counts with semantic cover/exchange. childCall evaluates remaining before invoking the supplied solver with that concrete Child and residual r. ExactBoundedChild includes success iff affordable ChildWithin, all returned G attained ExactChild minimum, and residual budget compliance; no solver is supplied. child_call_success, high_child_solver_iff and t1_child_solver_iff retain that child-specific IH. There is no mutual termination or final cut-union premise.

## T1Exchange.lean (full read)

actual_t1_pendant_exchange's complete caller assumptions are proper T/S, equal original label membership, original agreement, actual target CherryAt and actual source cut length1. The sole q is an original valid subtree. H is the original source split; agreement and +1 bound are derived. Its literal refinement and checked source P allow original_to_state. core_has_cherry produces an actual root-complement source component U (with arbitrary above-LCA siblings preserved). If the original pendant alternative gives singleton a or b, that endpoint is outside q and survives splitting. state_save_singleton finds the other endpoint's checked H block, excludes the singleton label by partition uniqueness, and invokes actual common-cherry reassignment with swapped endpoint orientation as needed, obtaining |G|+1=|H| exactly. state_to_original uses independently proved P source embeddings and returns original agreement/refinement. The +1 split and -1 reassignment cancel, giving |G|<=|F|. If original F refines P already it is returned directly. The proof supplies all surgery/ownership/state premises internally; none is an exchange premise from the caller.

## T1Split.lean (full read)

splitForest is literal BinaryExchange.splitAll of every original F block at the selected original source subtree. split_original_agreement derives preservation of both partitions, target and source restricted topology, and both original embedding systems; within-block separation is transported by descendant_agreed_split and between-block disjointness follows subset hulls. Source original disjointness gives at most one mixed block, so splitting adds at most one block. No exchange premise is imported from the caller. one_partition identifies the actual t1 partition, split_refines_one proves literal refinement, and a singleton endpoint outside the pendant subtree survives the split. The descendant-agreement transport and mixed-block count are targeted support obligations.

## CoreCherry.lean (full read)

first_exit follows original prefixes to the first path-exit child. PendantExcluded then excludes every nonendpoint selected leaf below the endpoint LCA. restrict_cherry_of_excluded inducts on the original source: when both endpoints descend into one child it transports exclusion and preserves any surviving exterior sibling, and at their split it proves each restricted side is its sole endpoint, including swapped child orientation. Proper source labels justify these singleton conclusions. core_excluded derives the needed exclusion from the actual pendant complement, and core_has_cherry supplies actual restrictions and rooted HasCherry without assuming exchange/refinement or suppressing above-LCA siblings.

## SourceBranches.lean (full read)

endpointBranch records the exact original terminalCut address, actual singleton child and one cut; endpoint_literal derives the address is an actual nonroot source leaf and paid equals list length. highBranch records the full original pendant list with paid=t. endpoint_components proves isolated q and every other original valid vertex in the root remainder, then witnesses a source leaf in each region using the distinct endpoint b. No suppressed displayed address is substituted. This gives original graph accounting for both endpoint costs.

## Priority.lean (full read)

PrioritySpec quantifies over every materialized candidate: one rejects all zero counts; high rejects all zero and one; hard2 requires every count exactly2. selected_spec obtains these universal conditions from failed actual find scans, including the final no-high scan and Nat exhaustion. selected_actual combines membership with candidate_sound. The intended rejection scope is genuinely all candidates, not only the chosen or previously visited list prefix. First-in-category order is executable find order; the proof spec only asserts category-level counts and membership.

## Consumer.lean (full read)

checked_nonempty and checked_nodup derive actual block nonemptiness and list uniqueness from partition/embedding checks. refined_length injects each actual source component into an F block via a shared original leaf and refinement, deriving |Q|<=|F| rather than assuming it. materialization_exists uses an actual selected source leaf; forest_length proves every filterMap entry survives. paid_budget_identity then uses the derived size inequality and paid+1=|P| to justify Nat subtraction and the original |F|-1 objective. ordinary_minimum assumes a distinct ExactChild IH for every literal high child, actual chosen return and minimum selection; branch cover supplies a feasible same-F child. It proves no solver or termination.

## Endpoints.lean (full read)

terminalCut scans all original vertices for an actual leaf subtree; soundness/existence derive LeafAt and a distinct other endpoint makes it nonroot. Singleton partition checks require proper source and both distinct endpoints, derive a nonempty complement, exact label multiplicities and source embedding separation. singleton_refinement uses original leaf hull uniqueness to prevent another block containing a and then places all other labels in the complement. ordinary/high branches_cover therefore passes the actual same F to one of the literal children, conditional on original agreement and actual target cherry. No paid budget is asserted here; subsequent consumers must supply it.

## Selector.lean (full read)

`cherries` traverses left then right and retains literal endpoint child order/original parent address; soundness and completeness are proved. `candidates` eagerly maps every cherry to its actual full source cut list before three find scans. `select` scans common, one, high, then first candidate hard2, including failed earlier scans. `Child` stores P, actual `P.filterMap restrict`, paid. Endpoint P is singleton plus source complement; high children cost1,1,t. `remaining` checks paid<=budget before Nat subtraction. `feasible` is ordinary original agreement plus original-label refinement; ExactChild is an attained child-specific minimum, not a solver. No optimum/partition enumeration call occurs in these executable definitions.

## Partition.lean (full read)

Pendant leaf lists are disjoint because cut addresses are incomparable; their flatten is Nodup under proper source labels. The root-complement filter gives exactly one occurrence of every source label, and endpoint a witnesses nonempty root remainder. `pendant_partition_check` therefore has actual source coverage/no absent labels. `subtree_hull` retains original vertices below the original cut root; `core_hull` stays in the live root region. `source_embeddings` maps the distinct component roots through rootBlock and proves pairwise original hull disjointness using residual-region separation. These are derived graph facts, not caller ownership assumptions. Together with Ordinary's graph theorem this establishes the materialization inputs pending exact rebuild/audit.

## Ordinary.lean (full read)

`cuts` aliases actual pendantOriginal; cuts_spec requires valid nonroot original child q, parent in minimalVertices[a,b], child outside. This excludes the upward LCA edge. pendantPartition appends root-complement labels after all pendant subtree leaf sets; length=t+1 is literal. cut_component/root_component characterize original residual walks, original_cover covers all original vertices, roots_separated separates component roots, and cut/root_leafset identify actual labels. no_leafless needs proper source plus endpoint presence and uses a source leaf below each cut or surviving endpoint a in the root region. actual_pendant_safety invokes the actual target cherry endpoint alternative; if neither singleton, both endpoints share a block and agreement_respects_pendant forces every F block to lie wholly on one side of every pendant edge. That yields refinement of one cut subtree or root complement. actual_high_safety merely adds the priority guard t>=3. No preassumed refinement or exchange premise occurs here. Source theorem dependencies will be traced in the isolated producer audit and targeted supporting source reads.
