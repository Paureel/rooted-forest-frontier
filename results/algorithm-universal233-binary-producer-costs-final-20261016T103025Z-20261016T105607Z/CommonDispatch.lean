import StateExpand
import Priority
import OutsideCore
import T1Exchange
import ForestConditional
import BuildSetup
namespace OrdinaryDispatch
open RMAF ForestState Universal233 Universal233.CherryBranching Universal233.HardParent

def commonFresh (T : Tree) : Nat := OrdinaryCommonSplit.Source.labelMax (leaves T)+1

theorem commonFresh_not_mem (T : Tree) : commonFresh T ∉ leaves T :=
 OrdinaryCommonSplit.Source.fresh_not_mem (leaves T) 1 (by decide)

theorem selected_common_ready {T S : Tree} {c : Candidate}
 (hp : proper (some T) [S]=true)
 (sel : select T S=some (.common,c)) :
 cherryReady (some T) [S] c.a c.b (commonFresh T)=true := by
 have nt := (proper_parts (some T) [S] hp).1
 have ns := (GenericForest.proper_source_labels T [S] hp S (by simp)).1
 have ch := (selected_actual sel).1
 have hab := cherry_distinct nt ch
 have labs := hasCherry_labels (actual_hasCherry ch)
 have perm : (leaves T).Perm (leaves S) := by
  have op := GenericForest.singleton_ordinary_proper T S hp
  simp only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at op
  exact op.2
 have aS : c.a∈leaves S := (perm.mem_iff).1 labs.1
 have bS : c.b∈leaves S := (perm.mem_iff).1 labs.2
 have hc : cuts S c.a c.b=[] := by
  rw [←(selected_actual sel).2]
  exact List.length_eq_zero_iff.1 (selected_spec sel).2
 have source := Rule5Classification.zero_cuts_hasCherry ns aS bS hab hc
 simpa [cherryReady,labels,Bool.and_eq_true,List.any_eq_true,and_assoc] using
  And.intro hp (And.intro hab (And.intro (commonFresh_not_mem T)
   (And.intro (hasCherry_bool (actual_hasCherry ch)) (hasCherry_bool source))))


abbrev CommonForest := List (List Nat)

/-- Mathematical correctness at one actual ordinary query. -/
def QueryExact (T S : Tree) (q : Nat) : Option CommonForest → Prop
 | none => ∀ F, agreement T S F=true → q<F.length-1
 | some F => agreement T S F=true ∧ F.length-1≤q ∧
     ∀G,agreement T S G=true → F.length≤G.length

def runCommonCherry (actual : Tree → Tree → Nat → Option CommonForest)
 (T S : Tree) (c : Candidate) (q : Nat) : Option CommonForest :=
 (actual (contract c.a c.b (commonFresh T) T)
   (contract c.a c.b (commonFresh T) S) q).map
   (fun F=>F.map (expandBlock c.a c.b (commonFresh T)))

theorem selected_common_label_decrease {T S : Tree} {c : Candidate}
 (hp : proper (some T) [S]=true) (sel : select T S=some (.common,c)) :
 (leaves (contract c.a c.b (commonFresh T) T)).length+1=(leaves T).length := by
 simpa [labels] using common_cherry_state_strict_decrease (some T) [S]
   c.a c.b (commonFresh T) (selected_common_ready hp sel)

theorem common_reduced_proper {T S : Tree} {a b z : Nat}
 (ready : cherryReady (some T) [S] a b z=true) :
 proper (some (contract a b z T)) [contract a b z S]=true := by
 have rr : proper (some T) [S]=true ∧ a≠b ∧ z∉leaves T ∧
   cherry a b T=true ∧ cherry a b S=true := by
  simpa [cherryReady,labels,Bool.and_eq_true,List.any_eq_true,and_assoc] using ready
 simpa using contraction_proper T [S] a b z rr.1 rr.2.2.2.1 rr.2.2.1 S (by simp) rr.2.2.2.2

theorem common_query_equivalence {T S : Tree} {a b z : Nat} (q : Nat)
 (ready : cherryReady (some T) [S] a b z=true) :
 (∃F,agreement T S F=true ∧ F.length-1≤q) ↔
 (∃G,agreement (contract a b z T) (contract a b z S) G=true ∧ G.length-1≤q) := by
 have hp : proper (some T) [S]=true := by
  have rr := ready
  simp only [cherryReady,Bool.and_eq_true] at rr
  exact rr.1.1.1.1
 have reduced := common_reduced_proper ready
 have equiv := common_cherry_decision_equivalence T [S] a b z q ready
 simpa only [ForestState.feasible,additionalCost,List.length_singleton,List.map_cons,List.map_nil,
   initial_state_agreement_iff T S _ hp,
   initial_state_agreement_iff (contract a b z T) (contract a b z S) _ reduced] using equiv

theorem common_expansion_original {T S : Tree} {a b z : Nat} {G : CommonForest}
 (ready : cherryReady (some T) [S] a b z=true)
 (hG : agreement (contract a b z T) (contract a b z S) G=true) :
 agreement T S (G.map (expandBlock a b z))=true := by
 have hp : proper (some T) [S]=true := by
  have rr := ready
  simp only [cherryReady,Bool.and_eq_true] at rr
  exact rr.1.1.1.1
 have reduced := common_reduced_proper ready
 apply (initial_state_agreement_iff T S _ hp).1
 apply common_cherry_expand_agreement T [S] G a b z ready
 simpa using (initial_state_agreement_iff _ _ G reduced).2 hG

/-- The only recursive premise is the contracted query, at unchanged budget.
The selected source gives a strict label decrease for well-founded recursion. -/
theorem selected_common_query_exact
 (actual : Tree → Tree → Nat → Option CommonForest) {T S : Tree} {c : Candidate} (q : Nat)
 (hp : proper (some T) [S]=true) (sel : select T S=some (.common,c))
 (ih : QueryExact (contract c.a c.b (commonFresh T) T)
   (contract c.a c.b (commonFresh T) S) q
   (actual (contract c.a c.b (commonFresh T) T)
     (contract c.a c.b (commonFresh T) S) q)) :
 QueryExact T S q (runCommonCherry actual T S c q) := by
 have ready := selected_common_ready hp sel
 have eqv := common_query_equivalence (T:=T) (S:=S) (a:=c.a) (b:=c.b) (z:=commonFresh T)
 unfold runCommonCherry
 cases h : actual (contract c.a c.b (commonFresh T) T)
     (contract c.a c.b (commonFresh T) S) q with
 | none =>
  simp only [h,Option.map_none,QueryExact] at ih ⊢
  intro F hF
  by_cases bound : F.length-1≤q
  · obtain ⟨G,hG,budget⟩ := (eqv q ready).1 ⟨F,hF,bound⟩
    have impossible := ih G hG
    omega
  · omega
 | some G =>
  simp only [h,Option.map_some,QueryExact] at ih ⊢
  refine ⟨common_expansion_original ready ih.1,by simpa using ih.2.1,?_⟩
  intro F hF
  obtain ⟨H,hH,cost⟩ := (eqv (F.length-1) ready).1 ⟨F,hF,Nat.le_refl _⟩
  have least := ih.2.2 H hH
  have pos := List.length_pos_iff.2 (DepthOne.agreement_nonempty T S F hF)
  simp only [List.length_map]
  omega

end OrdinaryDispatch
