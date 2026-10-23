/- Actual CommonReady from the independent leaf-multiset invariants and explicit
   reused selector/cut-zero structural reflection. CommonLift geometry stays open. -/
import CommonCoreV2
open RMAF ForestState Universal233 Universal233.HardParent
open Universal233.CherryBranching OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace IndependentCommon

theorem address_to_syntax {T : Tree} {p : RMAF.Vertex} {a b : Nat}
 (at : CoreGraph.CherryAt T p a b) : HasCherry a b T := by
 induction p generalizing T with
 | nil =>
  simp [CoreGraph.CherryAt,CoreGraph.subtree] at at
  subst T
  exact .here
 | cons side p ih =>
  cases T with
  | leaf x => simp [CoreGraph.CherryAt,CoreGraph.subtree] at at
  | node l r =>
   cases side
   · exact .left (ih at)
   · exact .right (ih at)

theorem selected_syntax {T S : Tree} {c : Candidate}
 (hp : DepthOne.proper T S=true) (selected : select T S=some (.common,c)) :
 HasCherry c.a c.b T ∧ HasCherry c.a c.b S := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts hp
 have actual := selected_actual selected
 have ht := address_to_syntax actual.1
 obtain ⟨rest,normal,_⟩ := contraction_normal ht 0 nt
 have apart : c.a≠c.b := by
  intro eq
  exact (List.nodup_cons.1 (normal.nodup nt)).1 (by simp [eq])
 have labels := syntax_labels ht
 have noCuts : cuts S c.a c.b=[] := by
  rw [←actual.2]
  exact List.length_eq_zero_iff.1 (selected_spec selected).2
 have hs := Rule5Classification.zero_cuts_hasCherry ns
   (perm.mem_iff.1 labels.1) (perm.mem_iff.1 labels.2) apart noCuts
 exact ⟨ht,hs⟩

theorem reverse_proper {T S : Tree} (hp : DepthOne.proper T S=true) :
 DepthOne.proper S T=true := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts hp
 simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
  And.intro ns (And.intro nt perm.symm)

theorem oriented_proper_own {T S : Tree} (hp : DepthOne.proper T S=true) (reverse : Bool) :
 DepthOne.proper (Oriented reverse T S).1 (Oriented reverse T S).2=true := by
 cases reverse
 · exact hp
 · exact reverse_proper hp

theorem commonPair_ready_from_selection {T S : Tree} {reverse : Bool} {c : Candidate}
 (hp : DepthOne.proper T S=true)
 (selected : select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.common,c)) :
 DepthOne.proper (commonPair T S reverse c).1 (commonPair T S reverse c).2=true ∧
 (leaves (commonPair T S reverse c).1).length<(leaves T).length := by
 have op := oriented_proper_own hp reverse
 have syntactic := selected_syntax op selected
 have pair := contraction_pair syntactic.1 syntactic.2 op
   (common_fresh (Oriented reverse T S).1)
 have sameLength : (leaves (Oriented reverse T S).1).length=(leaves T).length := by
  cases reverse
  · rfl
  · exact (IndependentReconstruction.proper_parts hp).2.2.length_eq.symm
 change DepthOne.proper (contract c.a c.b (commonFresh (Oriented reverse T S).1) (Oriented reverse T S).1)
   (contract c.a c.b (commonFresh (Oriented reverse T S).1) (Oriented reverse T S).2)=true ∧
   (leaves (contract c.a c.b (commonFresh (Oriented reverse T S).1) (Oriented reverse T S).1)).length<(leaves T).length
 exact ⟨pair.1,by rw [←sameLength];exact pair.2⟩

theorem actual_common_ready : IndependentReconstruction.CommonReady := by
 intro T S reverse c hp _ selected
 have sound := early_sound T S
 rw [selected] at sound
 exact commonPair_ready_from_selection hp sound

/- These are the exact original-forest geometry obligations that have NOT
   been independently reconstructed. They are hypotheses, not axioms. -/
def ExpansionGeometry : Prop := ∀ T S reverse c,
 DepthOne.proper T S=true → early T S=.common reverse c → ∀ G,
 agreement (commonPair T S reverse c).1 (commonPair T S reverse c).2 G=true →
 agreement T S (expandCommon T S reverse c G)=true

def CoarseningGeometry : Prop := ∀ T S reverse c,
 DepthOne.proper T S=true → early T S=.common reverse c → ∀ F,
 agreement T S F=true → ∃ H,
 agreement (commonPair T S reverse c).1 (commonPair T S reverse c).2 H=true ∧ H.length≤F.length

theorem common_lift_from_geometry (expansion : ExpansionGeometry) (coarsening : CoarseningGeometry) :
 IndependentReconstruction.CommonLift := by
 intro q T S reverse c answer hp _ selected exactness
 cases answer with
 | none =>
  simp only [Option.map_none,QueryExact] at exactness ⊢
  intro F hF
  obtain ⟨H,hH,le⟩ := coarsening T S reverse c hp selected F hF
  have low := exactness H hH
  omega
 | some G =>
  simp only [Option.map_some,QueryExact] at exactness ⊢
  refine ⟨expansion T S reverse c hp selected G exactness.1,?_,?_⟩
  · simpa [expandCommon] using exactness.2.1
  · intro F hF
    obtain ⟨H,hH,le⟩ := coarsening T S reverse c hp selected F hF
    have min := exactness.2.2 H hH
    simpa [expandCommon] using Nat.le_trans min le

theorem solver_after_common_ready
 (lift : IndependentReconstruction.CommonLift) (one : IndependentReconstruction.OneRule)
 (high : IndependentReconstruction.HighRule) (forward4 : IndependentReconstruction.ForwardRule4)
 (reverse4 : IndependentReconstruction.ReverseRule4) (hard : IndependentReconstruction.Hard2Rule)
 (nonrefusal : IndependentReconstruction.RejectImpossible) (q : Nat) :
 ∀ T S,DepthOne.proper T S=true → QueryExact T S q (FastOrdinary.solve q T S) :=
 IndependentReconstruction.solve_exact_from_local_rules actual_common_ready lift one high forward4 reverse4 hard nonrefusal q
end IndependentCommon
