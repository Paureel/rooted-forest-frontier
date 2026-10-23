import PaidChildren
namespace OrdinaryDispatch
open RMAF ForestState OutputState Universal233 Universal233.CherryBranching

theorem remaining_decreases {k r : Nat} {c : Child}
    (positive : 1≤c.paid) (hr : remaining k c=some r) : r<k := by
  unfold remaining at hr
  split at hr
  · have eq := Option.some.inj hr
    omega
  · contradiction

theorem three_children_literal {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (same : ∀x,x∈leaves T ↔ x∈leaves S) (ch : CoreGraph.CherryAt T p a b)
    (c : Child) (hc : c∈branches S a b) :
    partitionCheck (leaves S) c.partition=true ∧ pairwiseEmbeddings S c.partition=true ∧
    c.paid+1=c.partition.length ∧ c.sourceForest=OutputState.sourceForest S c.partition := by
  obtain ⟨hp,he,paid⟩ := branch_checks nt ns same ch hc
  refine ⟨hp,he,paid,?_⟩
  have cases : c=singletonChild S a ∨ c=singletonChild S b ∨ c=pendantChild S a b := by
    simpa [branches] using hc
  rcases cases with rfl|rfl|rfl <;> rfl

theorem three_children_paid {S : Tree} {a b : Nat}
    (positive : 1≤(cuts S a b).length) (c : Child) (hc : c∈branches S a b) : 1≤c.paid := by
  have cases : c=singletonChild S a ∨ c=singletonChild S b ∨ c=pendantChild S a b := by
    simpa [branches] using hc
  rcases cases with rfl|rfl|rfl
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact positive

/-- The actual three-child caller, with original source coverage already
proved, consumes only ordinary correctness strictly below its parent budget. -/
theorem three_children_complete
    (actual : Tree → Tree → Nat → Option Forest) (T S : Tree) (k : Nat)
    {p : RMAF.Vertex} {a b : Nat}
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (same : ∀x,x∈leaves T ↔ x∈leaves S) (ch : CoreGraph.CherryAt T p a b)
    (positive : 1≤(cuts S a b).length)
    (ih : ∀r,r<k → ForestMinCompletion.LocalOrdinaryIH r actual)
    (F : Forest) (hF : agreement T S F=true) (budget : F.length-1≤k) :
    ∃G,runChildren actual T S k (branches S a b)=some G ∧ G.length≤F.length := by
  apply runChildren_complete actual T S k (branches S a b) nt ns same
    (fun c hc => three_children_literal nt ns same ch c hc)
  · intro c hc r hr
    exact ih r (remaining_decreases (three_children_paid positive c hc) hr)
  · intro H hH
    obtain ⟨c,hc,feas⟩ := ordinary_branches_cover ns hH ch
    exact ⟨c,hc,H,feas,Nat.le_refl _⟩
  · exact hF
  · exact budget

/-- The literal t=1 rule runs just its cost1 pendant child. -/
theorem one_child_complete
    (actual : Tree → Tree → Nat → Option Forest) (T S : Tree) (k : Nat)
    {p : RMAF.Vertex} {a b : Nat}
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (same : ∀x,x∈leaves T ↔ x∈leaves S) (ch : CoreGraph.CherryAt T p a b)
    (one : (cuts S a b).length=1)
    (ih : ∀r,r<k → ForestMinCompletion.LocalOrdinaryIH r actual)
    (F : Forest) (hF : agreement T S F=true) (budget : F.length-1≤k) :
    ∃G,runChildren actual T S k [pendantChild S a b]=some G ∧ G.length≤F.length := by
  apply runChildren_complete actual T S k [pendantChild S a b] nt ns same
  · intro c hc
    have eq : c=pendantChild S a b := by simpa using hc
    subst c
    exact three_children_literal nt ns same ch _ (by simp [branches])
  · intro c hc r hr
    have eq : c=pendantChild S a b := by simpa using hc
    subst c
    exact ih r (remaining_decreases (by simpa [pendantChild,makeChild] using Nat.le_of_eq one.symm) hr)
  · intro H hH
    obtain ⟨G,hG,len,ref⟩ := actual_t1_pendant_exchange nt ns same hH ch one
    exact ⟨pendantChild S a b,by simp,G,⟨hG,ref⟩,len⟩
  · exact hF
  · exact budget
end OrdinaryDispatch
