/- Reused own frozen proof body; slim import slice, permanently CONTACTED. -/
/- Contacted partial repair: an explicit candidate has target agreement and recovers one block.
   Original source restriction agreement, source hulls and child refinement are still OPEN. -/
import SlimNonrefiningSingletonV3R4
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade
namespace ContactedRepair

theorem cherry_swap {T : Tree} {a b : Nat} (h : HasCherry a b T) : HasCherry b a T := by
 induction h with
 | here => exact .swap
 | swap => exact .here
 | left h ih => exact .left ih
 | right h ih => exact .right ih

theorem agreement_target_self {T S : Tree} {F : List (List Nat)}
 (hF : agreement T S F=true) : agreement T T F=true := by
 have old := hF
 simp only [agreement,Bool.and_eq_true] at old ⊢
 refine ⟨⟨⟨⟨old.1.1.1.1,old.1.1.1.1⟩,?_⟩,old.1.2⟩,old.1.2⟩
 apply List.all_eq_true.2
 intro B hb
 have before := List.all_eq_true.1 old.1.1.2 B hb
 unfold restrictionAgrees at before ⊢
 cases ht : restrict B T with
 | none => simp only [ht] at before;contradiction
 | some R => simp only [ht];exact iso_same (iso_refl R)

def repairCandidate (a b z : Nat) (X : List Nat) (F : List (List Nat)) :=
 let split := splitForest X F
 if [b]∈split then mergeCommon a b z split else mergeCommon b a z split

theorem candidate_target_half {T S U : Tree} {q p : Vertex} {a b z : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 (one : cuts S a b=[p]) (sub : CoreGraph.subtree S p=some U)
 {F : List (List Nat)} (hF : agreement T S F=true)
 (no : ¬VertexGeometry.Refines F (pendantPartition S a b)) (fresh : z∉leaves T) :
 agreement T T (repairCandidate a b z (leaves U) F)=true ∧
 (repairCandidate a b z (leaves U) F).length+1≤(splitForest (leaves U) F).length ∧
 (repairCandidate a b z (leaves U) F).length≤F.length := by
 have validSplit := original_clade_split_agreement T S U p F proper sub hF
 have singleton := nonrefining_singleton proper ch one sub hF no
 have nt := (IndependentReconstruction.proper_parts proper).1
 have selfProper : DepthOne.proper T T=true := by
  simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
   And.intro nt (And.intro nt (List.Perm.refl (leaves T)))
 have target := IndependentCommon.address_to_syntax ch
 have count := original_split_count sub (IndependentReconstruction.proper_parts proper).2.1 hF
 by_cases hb : [b]∈splitForest (leaves U) F
 · have merged := common_singleton_merge target target selfProper fresh _ (agreement_target_self validSplit) hb
   simp only [repairCandidate,hb,ite_true]
   exact ⟨merged.1,merged.2.1,by omega⟩
 · have ha : [a]∈splitForest (leaves U) F := by
    rcases singleton with ha|ha
    · exact split_keeps_singleton _ _ ha
    · exact False.elim (hb (split_keeps_singleton _ _ ha))
   have merged := common_singleton_merge (cherry_swap target) (cherry_swap target) selfProper fresh _
    (agreement_target_self validSplit) ha
   simp only [repairCandidate,hb,ite_false]
   exact ⟨merged.1,merged.2.1,by omega⟩

/- Precise unproved candidate obligation. No instance or theorem is supplied. -/
def CandidateOriginalSourceAndRefinement : Prop := ∀T S U q p a b z F,
 DepthOne.proper T S=true→CoreGraph.CherryAt T q a b→cuts S a b=[p]→
 CoreGraph.subtree S p=some U→agreement T S F=true→
 ¬VertexGeometry.Refines F (pendantPartition S a b)→z∉leaves T→
 agreement T S (repairCandidate a b z (leaves U) F)=true ∧
 VertexGeometry.Refines (repairCandidate a b z (leaves U) F) (pendantPartition S a b)
end ContactedRepair

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedRepair.cherry_swap
#print axioms ContactedRepair.cherry_swap
#check @ContactedRepair.agreement_target_self
#print axioms ContactedRepair.agreement_target_self
#check @ContactedRepair.candidate_target_half
#print axioms ContactedRepair.candidate_target_half
