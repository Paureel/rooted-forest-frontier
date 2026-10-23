import ChildForestBinding
namespace OrdinaryDispatch
open RMAF ForestState OutputState Universal233.CherryBranching

def childAnswers (actual : Tree → Tree → Nat → Option Forest) (T : Tree)
    (k : Nat) (children : List Child) : List Forest :=
  children.filterMap (childCall (forestChild actual T) k)

def ordinaryAccepted (T S : Tree) (k : Nat) (F : Forest) : Bool :=
  agreement T S F && decide (F.length-1 ≤ k)

/-- Actual affordable callbacks followed by one literal original check and
minimum selection. Each callback receives its own source forest and k-paid. -/
def runChildren (actual : Tree → Tree → Nat → Option Forest) (T S : Tree)
    (k : Nat) (children : List Child) : Option Forest :=
  best List.length (ordinaryAccepted T S k) (childAnswers actual T k children)

theorem runChildren_sound (actual : Tree → Tree → Nat → Option Forest)
    (T S : Tree) (k : Nat) (children : List Child) (G : Forest)
    (h : runChildren actual T S k children = some G) :
    agreement T S G = true ∧ G.length-1 ≤ k := by
  have hs := (best_spec List.length (ordinaryAccepted T S k) _ G h).2.1
  simpa [ordinaryAccepted,Bool.and_eq_true] using hs

/-- Conditional only on the named original source cover and actual literal
child checks. The callback IH is restricted to the emitted residual query. -/
theorem runChildren_complete (actual : Tree → Tree → Nat → Option Forest)
    (T S : Tree) (k : Nat) (children : List Child)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (same : ∀ x,x∈leaves T ↔ x∈leaves S)
    (literal : ∀ c,c∈children →
      partitionCheck (leaves S) c.partition=true ∧ pairwiseEmbeddings S c.partition=true ∧
      c.paid+1=c.partition.length ∧ c.sourceForest=OutputState.sourceForest S c.partition)
    (ih : ∀ c,c∈children → ∀ r,remaining k c=some r →
      ForestMinCompletion.LocalOrdinaryIH r actual)
    (cover : ∀ F,agreement T S F=true → ∃ c,c∈children ∧
      ∃ H,feasible T S c H ∧ H.length≤F.length)
    (F : Forest) (hF : agreement T S F=true) (hk : F.length-1≤k) :
    ∃ G,runChildren actual T S k children=some G ∧ G.length≤F.length := by
  obtain ⟨c,hc,H,hH,hlen⟩ := cover F hF
  obtain ⟨hp,he,paid,mat⟩ := literal c hc
  have rem := (remaining_correct k hp he paid).1 ⟨H,hH,by omega⟩
  obtain ⟨r,hr,hwithin⟩ := rem
  have exactAt := forest_child_exact_at T S c r actual (ih c hc r hr) nt ns same hp he mat
  obtain ⟨G,hG⟩ := exactAt.1.2 hwithin
  have hs := exactAt.2 G hG
  have haccepted : ordinaryAccepted T S k G=true := by
    have accepted := (remaining_correct k hp he paid).2 ⟨r,hr,G,hs.1.1,hs.2⟩
    -- The returned child itself has the original budget, by the paid identity.
    have hrefLen := refined_length hp he hs.1.1.1 hs.1.1.2
    have hrem : c.paid≤k ∧ r=k-c.paid := by
      unfold remaining at hr
      split at hr
      · exact ⟨by assumption,Option.some.inj hr.symm⟩
      · contradiction
    simp only [ordinaryAccepted,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hs.1.1.1,by omega⟩
  have member : G∈childAnswers actual T k children := by
    apply List.mem_filterMap.2
    exact ⟨c,hc,by simp [childCall,hr,hG]⟩
  obtain ⟨B,hB⟩ := best_exists List.length (ordinaryAccepted T S k) _ G member haccepted
  have least := (best_spec List.length (ordinaryAccepted T S k) _ B hB).2.2 G member haccepted
  have hmin := hs.1.2 H hH
  exact ⟨B,hB,Nat.le_trans least (Nat.le_trans hmin hlen)⟩

theorem runChildren_minimum (actual : Tree → Tree → Nat → Option Forest)
    (T S : Tree) (k : Nat) (children : List Child)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (same : ∀ x,x∈leaves T ↔ x∈leaves S)
    (literal : ∀ c,c∈children →
      partitionCheck (leaves S) c.partition=true ∧ pairwiseEmbeddings S c.partition=true ∧
      c.paid+1=c.partition.length ∧ c.sourceForest=OutputState.sourceForest S c.partition)
    (ih : ∀ c,c∈children → ∀ r,remaining k c=some r →
      ForestMinCompletion.LocalOrdinaryIH r actual)
    (cover : ∀ F,agreement T S F=true → ∃ c,c∈children ∧
      ∃ H,feasible T S c H ∧ H.length≤F.length)
    (G : Forest) (hG : runChildren actual T S k children=some G) :
    agreement T S G=true ∧ G.length-1≤k ∧
      ∀ F,agreement T S F=true → F.length-1≤k → G.length≤F.length := by
  refine ⟨(runChildren_sound actual T S k children G hG).1,
    (runChildren_sound actual T S k children G hG).2,?_⟩
  intro F hF hk
  obtain ⟨B,hB,least⟩ := runChildren_complete actual T S k children nt ns same literal ih cover F hF hk
  have eq : B=G := Option.some.inj (hB.symm.trans hG)
  simpa [eq] using least
end OrdinaryDispatch
