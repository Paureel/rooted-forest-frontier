/- Literal checked caller reconstructed; coverage and child exactness remain explicit. -/
import ReusedPayment
import PaidChildren
import QueryInterfaceSlice
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

end IndependentPaid

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @IndependentPaid.caller_sound
#print axioms IndependentPaid.caller_sound
#check @IndependentPaid.caller_complete
#print axioms IndependentPaid.caller_complete
#check @IndependentPaid.caller_query
#print axioms IndependentPaid.caller_query
