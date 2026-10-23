import RepairAssemblyV3
import EarlyInterfaceSliceV2
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace IndependentOneExchange
/- Exact frozen selected-domain interface; no author selector correctness is applied. -/
def SelectedOnePendantExchange : Prop := ∀ T S reverse c,
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected →
 early T S=.one reverse c →
 CoreGraph.CherryAt (Oriented reverse T S).1 c.parent c.a c.b →
 (cuts (Oriented reverse T S).2 c.a c.b).length=1 →
 ∀F,agreement (Oriented reverse T S).1 (Oriented reverse T S).2 F=true →
 ∃H,agreement (Oriented reverse T S).1 (Oriented reverse T S).2 H=true ∧
 H.length≤F.length ∧
 VertexGeometry.Refines H (pendantPartition (Oriented reverse T S).2 c.a c.b)
end IndependentOneExchange
namespace ContactedSource

theorem selected_one_pendant_exchange : IndependentOneExchange.SelectedOnePendantExchange := by
 intro T S reverse c proper rejected earlySelected ch one F hF
 have oriented : DepthOne.proper (Oriented reverse T S).1 (Oriented reverse T S).2=true := by
  cases reverse
  · exact proper
  · obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts proper
    change DepthOne.proper S T=true
    simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
     And.intro ns (And.intro nt perm.symm)
 exact one_pendant_exchange oriented ch one F hF
end ContactedSource

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedSource.selected_one_pendant_exchange
#print axioms ContactedSource.selected_one_pendant_exchange
