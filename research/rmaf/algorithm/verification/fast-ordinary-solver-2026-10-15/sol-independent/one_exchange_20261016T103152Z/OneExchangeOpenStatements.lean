/- OPEN propositions only: none is an axiom, supplied instance, or proved theorem. -/
import SelectedExchangeControls
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace IndependentOneExchange

/- First missing geometry. Label partition/refinement/count are already proved;
   agreement of the split forest (restriction isomorphism and both hull checks)
   is not proved. -/
def OriginalCladeSplitAgreement : Prop := ∀ (T S U : Tree) (p : Vertex) F,
 DepthOne.proper T S=true → CoreGraph.subtree S p=some U →
 agreement T S F=true → agreement T S (splitForest (leaves U) F)=true

/- Actual caller domain, both orientations. Cherry/count premises are recorded
   explicitly rather than silently invoking author selector correctness. -/
def SelectedOnePendantExchange : Prop := ∀ T S reverse c,
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected →
 early T S=.one reverse c →
 CoreGraph.CherryAt (Oriented reverse T S).1 c.parent c.a c.b →
 (cuts (Oriented reverse T S).2 c.a c.b).length=1 →
 ∀F,agreement (Oriented reverse T S).1 (Oriented reverse T S).2 F=true →
 ∃H,agreement (Oriented reverse T S).1 (Oriented reverse T S).2 H=true ∧
 H.length≤F.length ∧
 VertexGeometry.Refines H (pendantPartition (Oriented reverse T S).2 c.a c.b)

/- Even after a valid split, the source core is not an original common-cherry
   pair. An endpoint reattachment must be shown to preserve original target
   hull disjointness. The strict common-cherry merge alone does not supply it. -/
def SinglePendantRepair : Prop := ∀ (T S U : Tree) (p q : Vertex) a b F,
 DepthOne.proper T S=true → CoreGraph.CherryAt T q a b →
 cuts S a b=[p] → CoreGraph.subtree S p=some U →
 agreement T S F=true →
 ¬VertexGeometry.Refines F (pendantPartition S a b) →
 ∃H,agreement T S H=true ∧ H.length+1≤(splitForest (leaves U) F).length ∧
 VertexGeometry.Refines H (pendantPartition S a b)
end IndependentOneExchange
