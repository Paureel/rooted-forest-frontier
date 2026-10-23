/- Reused own frozen proof body; slim import slice, permanently CONTACTED. -/
/- OPEN propositions only: none is an axiom, supplied instance, or proved theorem. -/
import SlimSplitPartitionR3
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentOneExchange

/- First missing geometry. Label partition/refinement/count are already proved;
   agreement of the split forest (restriction isomorphism and both hull checks)
   is not proved. -/
def OriginalCladeSplitAgreement : Prop := ∀ (T S U : Tree) (p : Vertex) F,
 DepthOne.proper T S=true → CoreGraph.subtree S p=some U →
 agreement T S F=true → agreement T S (splitForest (leaves U) F)=true

end IndependentOneExchange

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
