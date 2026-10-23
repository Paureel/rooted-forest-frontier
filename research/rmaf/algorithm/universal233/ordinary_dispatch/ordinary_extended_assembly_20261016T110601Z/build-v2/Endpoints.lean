import PoolClassificationSelector
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

def terminalCut (S : Tree) (a : Nat) : Option RMAF.Vertex :=
 (vertices S).find? (fun q => decide (subtree S q = some (.leaf a)))

theorem terminalCut_sound {S : Tree} {a : Nat} {q : RMAF.Vertex}
 (h : terminalCut S a = some q) : LeafAt S q a := by
 unfold LeafAt
 have hh := List.find?_some (p := fun v => decide (subtree S v = some (.leaf a))) h
 exact of_decide_eq_true hh

theorem terminalCut_exists {S : Tree} {a : Nat} (ha : a ∈ leaves S) :
 ∃ q, terminalCut S a = some q ∧ LeafAt S q a := by
 cases h : terminalCut S a with
 | none =>
   obtain ⟨q,hq⟩ := leaf_exists ha
   have hm : q ∈ vertices S := (vertices_correct S q).2 hq.valid
   have all := List.find?_eq_none.1 h
   exact False.elim (all q hm (decide_eq_true (show subtree S q = some (.leaf a) from hq)))
 | some q => exact ⟨q,rfl,terminalCut_sound h⟩

theorem terminal_nonroot {S : Tree} {a b : Nat} {q : RMAF.Vertex}
 (hq : LeafAt S q a) (hb : b ∈ leaves S) (hab : a ≠ b) : q ≠ [] := by
 intro he
 subst q
 have hs : S = .leaf a := by simpa [LeafAt,subtree] using hq
 subst S
 exact hab (by simpa [leaves] using (show b = a from by simpa [leaves] using hb).symm)

theorem singleton_partition_check {S : Tree} {a b : Nat}
 (hn : (leaves S).Nodup) (ha : a ∈ leaves S) (hb : b ∈ leaves S) (hab : a ≠ b) :
 partitionCheck (leaves S) (singletonPartition S a) = true := by
 let C := (leaves S).filter (fun x => x != a)
 have hC : C.Nodup := hn.filter _
 have ne : C ≠ [] := by
   have hm : b ∈ C := by simp [C,hb,Ne.symm hab]
   intro he; rw [he] at hm; exact List.not_mem_nil hm
 have nonempty : (!C.isEmpty) = true := by
   cases he : C with
   | nil => exact False.elim (ne he)
   | cons x xs => rfl
 simp only [singletonPartition,partitionCheck,List.all_cons,List.all_nil,List.isEmpty_cons,
   Bool.not_false,Bool.and_true,Bool.and_eq_true]
 refine ⟨⟨⟨True.intro,nonempty⟩,?_⟩,?_⟩
 · apply List.all_eq_true.2
   intro x hx
   apply beq_iff_eq.2
   by_cases he : x = a
   · subst x
     have hc : a ∉ C := by simp [C]
     simpa [C,List.count_append,hC.count,hc]
   · have hc : x ∈ C := by simp [C,hx,he]
     simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.singleton_append]
     change (a :: C).count x = 1
     simp [List.count_cons,hC.count,hc,he,Ne.symm he]
 · apply List.all_eq_true.2
   intro x hx
   apply List.contains_iff_mem.2
   have hh : x = a ∨ x ∈ C := by simpa [C] using hx
   rcases hh with rfl | hh
   · exact ha
   · exact (List.mem_filter.1 hh).1

theorem singleton_source_embeddings {S : Tree} {a : Nat} (hn : (leaves S).Nodup) :
 pairwiseEmbeddings S (singletonPartition S a) = true := by
 rw [executable_pairwiseEmbeddings]
 change List.Pairwise _ [[a],(leaves S).filter (fun x => x != a)]
 constructor
 · intro C hc v ⟨hv,hw⟩
   have heC : C = (leaves S).filter (fun x => x != a) := by simpa using hc
   subst C
   obtain ⟨u,w,hu,hw',hp⟩ := hv
   have one : ∀ u, selectedLeaves [a] S u → LeafAt S u a := by
     intro u hu
     obtain ⟨x,hx,hs⟩ := (selected_decompose_label [a] S u).1 hu
     have he : x = a := by simpa using hx
     subst x
     exact (leafAt_selected S u a).2 hs
   have he := leaf_unique hn (one u hu) (one w hw')
   subst w
   have ve : v = u := path_identical v u hp
   subst v
   have hm := (minimalVertices_terminal _ S u a (one u hu)).1 ((minimalVertices_correct _ S u).2 hw)
   simpa using hm
 · simp

theorem singleton_refinement {T S : Tree} {F : List (List Nat)}
 (ha : agreement T S F = true) {a : Nat} (hs : [a] ∈ F) :
 Refines F (singletonPartition S a) := by
 have checks := source_agreement_checks ha
 have hal : a ∈ leaves S := block_labels checks.1 hs (by simp)
 obtain ⟨v,hv⟩ := leaf_exists hal
 intro B hB
 by_cases hm : a ∈ B
 · have he : B = [a] := checked_support_unique S F checks.2 B [a] hB hs v
     ((minimalVertices_terminal B S v a hv).2 hm)
     ((minimalVertices_terminal [a] S v a hv).2 (by simp))
   subst B
   exact ⟨[a],by simp [singletonPartition],fun _ h => h⟩
 · refine ⟨(leaves S).filter (fun x => x != a),by simp [singletonPartition],?_⟩
   intro x hx
   have hn : x ≠ a := fun he => hm (he ▸ hx)
   simp [block_labels checks.1 hB hx,hn]

theorem ordinary_branches_cover {T S : Tree} {F : List (List Nat)}
 (hn : (leaves S).Nodup) (ha : agreement T S F = true)
 {p : RMAF.Vertex} {a b : Nat} (hc : CherryAt T p a b) :
 ∃ c, c ∈ branches S a b ∧ feasible T S c F := by
 rcases actual_pendant_safety hn ha hc with hs | hs | href
 · exact ⟨singletonChild S a,by simp [branches],ha,singleton_refinement ha hs⟩
 · exact ⟨singletonChild S b,by simp [branches],ha,singleton_refinement ha hs⟩
 · exact ⟨pendantChild S a b,by simp [branches],ha,href⟩
theorem high_branches_cover {T S : Tree} {F : List (List Nat)}
 (hn : (leaves S).Nodup) (ha : agreement T S F = true)
 {p : RMAF.Vertex} {a b : Nat} (hc : CherryAt T p a b)
 (_high : 3 ≤ (cuts S a b).length) :
 ∃ c, c ∈ branches S a b ∧ feasible T S c F := ordinary_branches_cover hn ha hc
end Universal233.CherryBranching
