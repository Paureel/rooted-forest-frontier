-- Own universal first stage of the requested dichotomy.
import EndpointRight22
open RMAF Universal233
namespace OwnHigh
theorem singleton_or_shared (T : Tree) (p : Vertex) (a b : Nat)
    (F : List (List Nat)) (hc : CoreGraph.CherryAt T p a b)
    (hpart : partitionCheck (leaves T) F = true)
    (hemb : pairwiseEmbeddings T F = true) :
    [a] ∈ F ∨ [b] ∈ F ∨ ∃ P ∈ F, a ∈ P ∧ b ∈ P := by
  by_cases has : [a] ∈ F
  · exact Or.inl has
  by_cases hbs : [b] ∈ F
  · exact Or.inr (Or.inl hbs)
  obtain ⟨P,hp,ha⟩ := label_block (leaves T) F hpart a (cherry_a_mem T p a b hc)
  obtain ⟨Q,hq,hb⟩ := label_block (leaves T) F hpart b (cherry_b_mem T p a b hc)
  by_cases he : P = Q
  · exact Or.inr (Or.inr ⟨P,hp,ha,he.symm ▸ hb⟩)
  have hP : P ≠ [a] := fun he => has (he ▸ hp)
  have hQ : Q ≠ [b] := fun he => hbs (he ▸ hq)
  have hPa := other_of_not_singleton P a (block_nodup _ _ hpart P hp) ha hP
  have hQb := other_of_not_singleton Q b (block_nodup _ _ hpart Q hq) hb hQ
  have hpv := cherry_in_minimal T p a b P hc ha (block_subset _ _ hpart P hp) hPa
  have hqv := cherry_in_minimal_right T p a b Q hc hb (block_subset _ _ hpart Q hq) hQb
  have hd := disjoint_pair T F P Q hemb hp hq he
  have hd' : ∀ v ∈ minimalVertices P T, (minimalVertices Q T).contains v = false := by
    simpa only [disjointVertices, List.all_eq_true, Bool.not_eq_true'] using hd
  have hnot := hd' p hpv
  have hyes : (minimalVertices Q T).contains p = true := List.contains_iff_mem.mpr hqv
  exact False.elim (Bool.noConfusion (hyes.symm.trans hnot))
theorem agreement_singleton_or_shared (T S : Tree) (p : Vertex) (a b : Nat)
    (F : List (List Nat)) (hc : CoreGraph.CherryAt T p a b)
    (hag : agreement T S F = true) :
    [a] ∈ F ∨ [b] ∈ F ∨ ∃ P ∈ F, a ∈ P ∧ b ∈ P := by
  simp only [agreement, Bool.and_eq_true] at hag
  exact singleton_or_shared T p a b F hc hag.1.1.1.1 hag.1.2
#print axioms singleton_or_shared
#print axioms agreement_singleton_or_shared
#print agreement_singleton_or_shared
end OwnHigh
