# Bounded-size forest frontier interface

Import BoundedFrontier. Namespace GenericForest.FrontierSize.

frontier_query_support proves both trees in every retained ordinary query use
only labels of the current forest target. frontier_query_size consequently
bounds both query leaf counts by (ForestState.labels T).length. The singleton
case can have equal size; no strict decrease is claimed there. All actual raw
branch occurrences and failed scheduler queries remain in the frozen frontier.

frontier_work_bound_on_queries requires the callback bound W<=D*c^r only for
actual frontier members. SizeCappedOrdinaryBillBound W N Q c D quantifies only
proper pairs with BOTH leaf counts <= N and r<=Q. The corresponding
frontier_work_bound_size_capped uses the proved support/size bound, current
size<=N and q<=Q. The source_work_bound_on_queries and
source_work_bound_size_capped interfaces combine this callback bill with the
separate frozen zero-ordinaryWork LocalOverheadBound and give

    sourceWork <= (D + geometric(c)*K)*c^q,
    geometric(c)=1/(1-2/c), c>2.

D is paid once. No all-size OrdinaryBillBound or global semantic OrdinaryIH is
a premise. K remains the explicit local overhead obligation. This first seal
covers only the necessary bounded-size interface; the concrete polynomial K
will continue in a new disjoint directory. All main milestones and independent
acceptance remain OPEN. This is source-level accounting, not a compiler/runtime
IR trace or primitive/source-bill correspondence acceptance.
