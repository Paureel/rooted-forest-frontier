/- Literal checked caller reconstructed; coverage and child exactness remain explicit. -/
import PartitionPaymentV2
open RMAF ForestState OutputState Universal233 Universal233.CherryBranching OrdinaryDispatch
namespace IndependentPaid

def Literal (S : Tree) (children : List Child) : Prop := ∀c∈children,
 partitionCheck (leaves S) c.partition=true ∧ pairwiseEmbeddings S c.partition=true ∧
 c.paid+1=c.partition.length ∧ c.sourceForest=OutputState.sourceForest S c.partition

def Coverage (T S : Tree) (children : List Child) : Prop := ∀F,agreement T S F=true→
 ∃c∈children,∃H,feasible T S c H ∧ H.length≤F.length

def CurrentChildren (actual : Tree→Tree→Nat→Option Forest) (T S : Tree) (q : Nat)
 (children : List Child) : Prop := ∀c∈children,∀r,remaining q c=some r→
 ExactChildAt T S (forestChild actual T) c r

theorem caller_sound (actual : Tree→Tree→Nat→Option Forest) (T S : Tree) (q : Nat)
 (children : List Child) {G : Forest} (h : runChildren actual T S q children=some G) :
 agreement T S G=true ∧ G.length-1≤q := by
 have v := (best_return List.length (ordinaryAccepted T S q) _ h).2.1
 simpa only [ordinaryAccepted,Bool.and_eq_true,decide_eq_true_eq] using v

theorem caller_complete (actual : Tree→Tree→Nat→Option Forest) (T S : Tree) (q : Nat)
 (children : List Child) (ns : (leaves S).Nodup) (lit : Literal S children)
 (ex : CurrentChildren actual T S q children) (cover : Coverage T S children)
 (F : Forest) (hF : agreement T S F=true) (budget : F.length-1≤q) :
 ∃G,runChildren actual T S q children=some G ∧ G.length≤F.length := by
 obtain ⟨c,hc,H,hH,len⟩ := cover F hF
 obtain ⟨part,emb,paid,mat⟩ := lit c hc
 have identity := paid_identity ns part paid hH
 have affordable : c.paid≤q := by omega
 let r := q-c.paid
 have hr : remaining q c=some r := by simp only [remaining,affordable,ite_true];rfl
 have within : ChildWithin T S c r := ⟨H,hH,by dsimp [r];omega⟩
 have exactAt := ex c hc r hr
 obtain ⟨G,hG⟩ := exactAt.1.2 within
 have spec := exactAt.2 G hG
 have returnedIdentity := paid_identity ns part paid spec.1.1
 have rSpec := remaining_spec hr
 have accepted : ordinaryAccepted T S q G=true := by
  simp only [ordinaryAccepted,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨spec.1.1.1,by omega⟩
 have member : G∈childAnswers actual T q children := by
  apply List.mem_filterMap.2
  exact ⟨c,hc,by simp only [childCall,hr,Option.bind_some];exact hG⟩
 obtain ⟨B,hB,least⟩ := best_witness List.length (ordinaryAccepted T S q) _ member accepted
 exact ⟨B,hB,Nat.le_trans least (Nat.le_trans (spec.1.2 H hH) len)⟩

theorem caller_query (actual : Tree→Tree→Nat→Option Forest) (T S : Tree) (q : Nat)
 (children : List Child) (ns : (leaves S).Nodup) (lit : Literal S children)
 (ex : CurrentChildren actual T S q children) (cover : Coverage T S children) :
 QueryExact T S q (runChildren actual T S q children) := by
 cases h : runChildren actual T S q children with
 | none =>
  intro F hF
  by_cases budget : F.length-1≤q
  · obtain ⟨G,hG,_⟩ := caller_complete actual T S q children ns lit ex cover F hF budget
    rw [h] at hG
    contradiction
  · omega
 | some G =>
  have sound := caller_sound actual T S q children h
  refine ⟨sound.1,sound.2,?_⟩
  intro F hF
  by_cases budget : F.length-1≤q
  · obtain ⟨B,hB,least⟩ := caller_complete actual T S q children ns lit ex cover F hF budget
    have eq : B=G := Option.some.inj (hB.symm.trans h)
    simpa only [eq] using least
  · omega

theorem strict_local_ih {q r : Nat} (below : IndependentReconstruction.BelowBudget q) (rq : r<q) :
 ForestMinCompletion.LocalOrdinaryIH r (IndependentReconstruction.OwnPaid q) := by
 constructor
 · intro T S b F br proper returned
   have bq : b<q := by omega
   have actual : OrdinaryDispatch.FastOrdinary.solve b T S=some F := by
    simpa only [IndependentReconstruction.OwnPaid,dif_pos bq] using returned
   have exactness := below b bq T S proper
   rw [actual] at exactness
   exact exactness
 · intro T S b F br proper hF budget
   have bq : b<q := by omega
   have exactness := below b bq T S proper
   cases h : OrdinaryDispatch.FastOrdinary.solve b T S with
   | none =>
    rw [h] at exactness
    have no := exactness F hF
    omega
   | some G => exact ⟨G,by simp only [IndependentReconstruction.OwnPaid,dif_pos bq,h]⟩

/- Explicit reused conditional generic forest solver fact; no independent credit. -/
theorem current_children_from_strict {q : Nat} {T S : Tree} {children : List Child}
 (hp : DepthOne.proper T S=true) (lit : Literal S children)
 (positive : ∀c∈children,1≤c.paid) (below : IndependentReconstruction.BelowBudget q) :
 CurrentChildren (IndependentReconstruction.OwnPaid q) T S q children := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts hp
 intro c hc r hr
 obtain ⟨part,emb,_,mat⟩ := lit c hc
 exact forest_child_exact_at T S c r (IndependentReconstruction.OwnPaid q)
  (strict_local_ih below (remaining_strict (positive c hc) hr)) nt ns
  (fun x=>perm.mem_iff) part emb mat

theorem checked_caller_from_strict {q : Nat} {T S : Tree} {children : List Child}
 (hp : DepthOne.proper T S=true) (lit : Literal S children)
 (positive : ∀c∈children,1≤c.paid) (below : IndependentReconstruction.BelowBudget q)
 (cover : Coverage T S children) :
 QueryExact T S q (runChildren (IndependentReconstruction.OwnPaid q) T S q children) :=
 caller_query _ T S q children (IndependentReconstruction.proper_parts hp).2.1 lit
  (current_children_from_strict hp lit positive below) cover
end IndependentPaid
