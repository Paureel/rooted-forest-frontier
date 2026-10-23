import Budget
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

theorem cuts_swap (S : Tree) (a b : Nat) : cuts S a b = cuts S b a := pendantOriginal_swap S a b

theorem pendantPartition_swap (S : Tree) (a b : Nat) :
 pendantPartition S a b = pendantPartition S b a := by
 simp only [pendantPartition,coreLabels,cuts_swap S a b]

theorem actual_t1_unordered_exchange {T S : Tree} {F : List (List Nat)}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (ha : agreement T S F = true) {a b : Nat} (hc : ActualCherry T a b)
 (one : (cuts S a b).length = 1) :
 ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧ Refines G (pendantPartition S a b) := by
 obtain ⟨p,hc | hc⟩ := hc
 · exact actual_t1_pendant_exchange hnT hnS same ha hc one
 · have one' : (cuts S b a).length = 1 := by rw [←cuts_swap S a b]; exact one
   obtain ⟨G,hG,hlen,href⟩ := actual_t1_pendant_exchange hnT hnS same ha hc one'
   exact ⟨G,hG,hlen,by rw [pendantPartition_swap S a b]; exact href⟩

theorem actual_high_unordered_safety {T S : Tree} {F : List (List Nat)}
 (hnS : (leaves S).Nodup) (ha : agreement T S F = true)
 {a b : Nat} (hc : ActualCherry T a b) (_high : 3 ≤ (cuts S a b).length) :
 [a] ∈ F ∨ [b] ∈ F ∨ Refines F (pendantPartition S a b) := by
 obtain ⟨p,hc | hc⟩ := hc
 · exact actual_pendant_safety hnS ha hc
 · rcases actual_pendant_safety hnS ha hc with hs | hs | href
   · exact Or.inr (Or.inl hs)
   · exact Or.inl hs
   · exact Or.inr (Or.inr (by rw [pendantPartition_swap S a b]; exact href))
end Universal233.CherryBranching
