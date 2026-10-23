import Rule4SourceExchange
import Parents

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

theorem source_sibling_singleton {T S : Tree} {F : List (List Nat)}
    (hF : agreement T S F = true) {a c : Nat} (hc : HasCherry a c S)
    {B : List Nat} (hB : B ∈ F) (ha : a ∈ B) (hcB : c ∉ B)
    (hd : ∃ d, d ∈ B ∧ d ∈ leaves S ∧ d ≠ a) : [c] ∈ F := by
  have checks := source_agreement_checks hF
  have make (p : RMAF.Vertex) (sa sc : Bool)
      (hla : LeafAt S (p ++ [sa]) a) (hlc : LeafAt S (p ++ [sc]) c) : [c] ∈ F := by
    have hparent := leaf_parent_hull hla B ha hd
    obtain ⟨C,hC,hcC⟩ := partitionCheck_covers _ F checks.1 c (leafAt_label S _ c hlc)
    have only : ∀ x, x ∈ C → x = c := by
      intro x hx
      by_cases he : x = c
      · exact he
      have hpc := leaf_parent_hull hlc C hcC ⟨x,hx,block_labels checks.1 hC hx,he⟩
      have hCB := checked_support_unique S F checks.2 C B hC hB p hpc hparent
      exact False.elim (hcB (hCB ▸ hcC))
    have he := block_singleton_of_only checks.1 hC hcC only
    simpa [he] using hC
  obtain ⟨p,hp | hp⟩ := hasCherry_address hc
  · exact make p false true (cherry_left hp) (cherry_right hp)
  · exact make p true false (cherry_right hp) (cherry_left hp)

theorem yes_no_count (B : List Nat) (q : Nat → Bool) (x : Nat) :
    (yes B q).count x + (no B q).count x = B.count x := by
  induction B with
  | nil => simp [yes,no]
  | cons y ys ih =>
    cases hq : q y <;> simp [yes,no,hq,List.count_cons] at ih ⊢ <;> omega

/-- Pure literal block replacement. No graph safety enters the count identity. -/
theorem replace_two_partition (L B : List Nat) (b : Nat) (R : List (List Nat))
    (q : Nat → Bool) (hF : partitionCheck L (B :: [b] :: R) = true)
    (hD : yes B q ≠ []) :
    partitionCheck L (yes B q :: (b :: no B q) :: R) = true := by
  obtain ⟨hne,hcount,hlabels⟩ := partition_parts L _ hF
  apply partition_intro
  · intro C hC
    simp only [List.mem_cons] at hC
    rcases hC with rfl | rfl | hC
    · exact hD
    · simp
    · exact hne C (by simp [hC])
  · intro x hx
    have hh := hcount x hx
    have hc := yes_no_count B q x
    simp only [List.flatten_cons,List.count_append,List.count_cons,List.count_nil,List.flatten_nil,List.append_nil] at hh ⊢
    omega
  · intro x hx
    have cases : x ∈ yes B q ∨ x ∈ b :: no B q ∨ x ∈ R.flatten := by simpa [or_assoc] using hx
    apply hlabels x
    rcases cases with hh | hh | hh
    · exact List.mem_flatten.2 ⟨B,by simp,(List.mem_filter.1 hh).1⟩
    · rcases List.mem_cons.1 hh with rfl | hh
      · simp
      · exact List.mem_flatten.2 ⟨B,by simp,(List.mem_filter.1 hh).1⟩
    · simp [hh]

/-- Full disputed Rule4 exchange on original trees and actual original F.
Every topology and every outside-component clearance conclusion is constructed.
Only literal source path/cherry guards, ordinary agreement and label properness
are supplied. R may be empty, contain arbitrary untouched components, or have
labels also present in B outside the path's LCA clade. -/
theorem actual_grouped_exchange {T S : Tree}
    (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
    {a b c : Nat} (hab : a ≠ b) (hcT : HasCherry a b T) (hcS : HasCherry a c S)
    {q r : RMAF.Vertex} (hcuts : (pendantOriginal S a b).Perm [q,r])
    (hql : subtreeLabels S q = [c])
    (B : List Nat) (R : List (List Nat))
    (hF : agreement T S (B :: [b] :: R) = true)
    (ha : a ∈ B) (hcB : c ∉ B)
    (hd : ∃ d, d ∈ B ∧ d ∈ subtreeLabels S r) :
    let D := yes B ((subtreeLabels S r).contains ·)
    let K := no B ((subtreeLabels S r).contains ·)
    let G := D :: (b :: K) :: R
    agreement T S G = true ∧ G.length = (B :: [b] :: R).length ∧
      VertexGeometry.Refines G (literalThree S q r) := by
  let F := B :: [b] :: R
  let D := yes B ((subtreeLabels S r).contains ·)
  let K := no B ((subtreeLabels S r).contains ·)
  let E := b :: K
  let G := D :: E :: R
  change agreement T S G = true ∧ G.length = F.length ∧ VertexGeometry.Refines G (literalThree S q r)
  have parts := agreement_parts T S F hF
  have checks := source_agreement_checks hF
  have hB : B ∈ F := by simp [F]
  have hbb : [b] ∈ F := by simp [F]
  have hal : a ∈ leaves S := block_labels checks.1 hB ha
  have hbl : b ∈ leaves S := block_labels checks.1 hbb (by simp)
  have hq : q ∈ pendantOriginal S a b := two_cut_mem_left hcuts
  have hr : r ∈ pendantOriginal S a b := two_cut_mem_right hcuts
  have hrv := (pendantOriginal_spec S a b r).1 hr
  have haR := source_label_outside_pendant hr (Or.inl rfl) hal
  have hbR := source_label_outside_pendant hr (Or.inr rfl) hbl
  have haK : a ∈ K := by simp [K,no,ha,haR]
  have hneK : K ≠ [] := by intro he; simpa [he] using haK
  have hneD : D ≠ [] := by
    obtain ⟨d,hdB,hdR⟩ := hd
    have hm : d ∈ D := by simp [D,yes,hdB,hdR]
    intro he; simpa [he] using hm
  have hbB : b ∉ B := by
    intro hh
    have eq := shared_label_block_equal checks.1 checks.2 hB hbb hh (by simp)
    have hab' : a = b := by simpa [eq] using ha
    exact hab hab'
  have hcc : [c] ∈ F := by
    obtain ⟨d,hdB,hdR⟩ := hd
    have hdl : d ∈ leaves S := block_labels checks.1 hB hdB
    have hda : d ≠ a := fun he => haR (he ▸ hdR)
    exact source_sibling_singleton hF hcS hB ha hcB ⟨d,hdB,hdl,hda⟩
  have hBK : K ⊆ B := by intro x hx; exact (List.mem_filter.1 hx).1
  have hBD : D ⊆ B := by intro x hx; exact (List.mem_filter.1 hx).1
  have hshapeD : restrictionAgrees T S D = true := by
    obtain ⟨d,hdB,hdR⟩ := hd
    have hm : d ∈ D := by simp [D,yes,hdB,hdR]
    exact restrictionAgrees_sub T S B D (parts.2.2.1 B hB) hBD
      ⟨d,hm,block_labels parts.1 hB hdB⟩
  let C := (leaves S).filter (fun x => !(subtreeLabels S q).contains x && !(subtreeLabels S r).contains x)
  have hKC : K ⊆ C := by
    intro x hx
    have hxB := hBK hx
    have hxc : x ≠ c := fun he => hcB (he ▸ hxB)
    have hxR : x ∉ subtreeLabels S r := by simpa using (List.mem_filter.1 hx).2
    simp [C,hql,block_labels checks.1 hB hxB,hxc,hxR]
  have hend := hard2_endpoints_in_root hq hr hal hbl
  obtain ⟨U,hU,hcU⟩ := literal_root_cherry hnS hal hbl hab hcuts
  have hshapeK : restrictionAgrees T S K = true :=
    restrictionAgrees_sub T S B K (parts.2.2.1 B hB) hBK
      ⟨a,haK,block_labels parts.1 hB ha⟩
  have hshapeE : restrictionAgrees T S E = true :=
    retained_cherry_graft_agrees hnT hnS hcT C hU hcU K hKC hend.2 haK
      (fun hh => hbB (hBK hh)) hshapeK
  obtain ⟨V,hV⟩ := hrv.1
  have hlabels := subtreeLabels_eq_leaves hV
  have ht : treeAt S r = some V := by rw [treeAt_eq_subtree]; exact hV
  have hsplit := (descendant_agreed_split T S V r B hnS ht (parts.2.2.1 B hB)).2.1
  have hsplit' : disjointVertices (minimalVertices D T) (minimalVertices K T) = true := by
    simpa only [D,K,hlabels] using hsplit
  have hDKT := (executable_disjointVertices T D K).1 hsplit'
  have hnaD : a ∉ D := by simp [D,yes,haR]
  have hnbD : b ∉ D := by simp [D,yes,hbR]
  have hDET : Disj T D E := (executable_disjointVertices T D E).1
    (extension_clear_unordered hnT hcT D K E haK hnaD hnbD hsplit'
      (by intro x hx; simpa [E,List.mem_cons,or_comm] using hx))
  have hDES : Disj S D E := by
    apply original_clade_clear hnS ht D E
      (by intro x hx; exact block_labels checks.1 hB (hBD hx))
      (by intro x hx; rcases List.mem_cons.1 hx with rfl | hx; exact hbl; exact block_labels checks.1 hB (hBK hx))
    · intro x hx; have hh := (List.mem_filter.1 hx).2; simpa only [hlabels,List.contains_iff_mem] using hh
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simpa only [hlabels] using hbR
      · have hh := (List.mem_filter.1 hx).2
        simpa [hlabels] using hh
  have untouched (H : List Nat) (hH : H ∈ R) :
      H ∈ F ∧ H ≠ B ∧ H ≠ [b] ∧ a ∉ H ∧ b ∉ H := by
    have hH' : H ∈ F := by simp [F,hH]
    have hflat := partition_flatten_nodup (leaves S) F checks.1
    have hnBR : (B ++ ([b] ++ R.flatten)).Nodup := by simpa [F] using hflat
    obtain ⟨_,_,hBrest⟩ := List.nodup_append.1 hnBR
    have haH : a ∉ H := by
      intro hh
      exact hBrest a ha a (by simp [List.mem_flatten.2 ⟨H,hH,hh⟩]) rfl
    have hnrest : ([b] ++ R.flatten).Nodup := (List.nodup_append.1 hnBR).2.1
    have hbH : b ∉ H := by
      intro hh
      exact (List.nodup_append.1 hnrest).2.2 b (by simp) b
        (List.mem_flatten.2 ⟨H,hH,hh⟩) rfl
    refine ⟨hH',?_,?_,haH,hbH⟩
    · intro he; exact haH (he ▸ ha)
    · intro he; exact hbH (by simp [he])
  have hES := source_extension_all_clear hnS hF hab hcuts hql hB ha hcB hbb hcc hd
  have newpair (W : Tree) (hp : F.Pairwise (Disj W)) (hDE : Disj W D E)
      (hER : ∀ H, H ∈ R → Disj W E H) : G.Pairwise (Disj W) := by
    have hRR : R.Pairwise (Disj W) := (List.pairwise_cons.1 (List.pairwise_cons.1 hp).2).2
    apply List.pairwise_cons.2
    refine ⟨?_,List.pairwise_cons.2 ⟨hER,hRR⟩⟩
    intro H hH
    rcases List.mem_cons.1 hH with rfl | hH
    · exact hDE
    · exact disj_mono (pairwise_mem (fun _ _ h => disj_symm h) F hp B H hB
        (untouched H hH).1 (Ne.symm (untouched H hH).2.1)) hBD (fun _ hx => hx)
  have hpT : G.Pairwise (Disj T) := newpair T parts.2.2.2.1 hDET (by
    intro H hH
    obtain ⟨hH',hHB,hHb,haH,hbH⟩ := untouched H hH
    have hHK : Disj T H K := disj_mono (checked_blocks_clear (agreement_graph_factors T S F hF).1 hH' hB hHB)
      (fun _ hx => hx) hBK
    exact disj_symm ((executable_disjointVertices T H E).1
      (extension_clear_unordered hnT hcT H K E haK haH hbH
        ((executable_disjointVertices T H K).2 hHK)
        (by intro x hx; simpa [E,List.mem_cons,or_comm] using hx))))
  have hpS : G.Pairwise (Disj S) := newpair S parts.2.2.2.2 hDES (by
    intro H hH
    have hh := untouched H hH
    exact disj_symm (hES H hh.1 hh.2.1 hh.2.2.1))
  have hnew : agreement T S G = true := by
    unfold agreement
    simp only [Bool.and_eq_true,List.all_eq_true,executable_pairwiseEmbeddings]
    refine ⟨⟨⟨⟨replace_two_partition (leaves T) B b R _ parts.1 hneD,
      replace_two_partition (leaves S) B b R _ parts.2.1 hneD⟩,?_⟩,hpT⟩,hpS⟩
    intro H hH
    rcases List.mem_cons.1 hH with rfl | hH
    · exact hshapeD
    · rcases List.mem_cons.1 hH with rfl | hH
      · exact hshapeE
      · exact parts.2.2.1 H (untouched H hH).1
  have hnewchecks := source_agreement_checks hnew
  have noSingleton (x y : Nat) (hx : x ∈ E) (hy : y ∈ E) (hne : x ≠ y) : [x] ∉ G := by
    intro hh
    have he : [x] = E := shared_label_block_equal hnewchecks.1 hnewchecks.2 hh (by simp [G]) (by simp) hx
    have hy' : y = x := by simpa [←he] using hy
    exact hne hy'.symm
  have haE : a ∈ E := by simp [E,haK]
  have hbE : b ∈ E := by simp [E]
  obtain ⟨q',r',hcuts',_,_,hcovers⟩ := actual_hard2_unordered_safety hnS hnew
    (hasCherry_address hcT) (two_cut_length hcuts)
  refine ⟨hnew,by simp [G,F],?_⟩
  rcases hcovers with hsa | hsb | hcover
  · exact False.elim (noSingleton a b haE hbE hab hsa)
  · exact False.elim (noSingleton b a hbE haE (Ne.symm hab) hsb)
  · exact refines_two_cut_order hcuts hcuts' hcover
end Universal233.Rule4

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

/-- The actual disputed source exchange for EVERY original forest order.
There is no partition-refinement or exchange premise in the hypotheses. -/
theorem actual_original_exchange {T S : Tree}
    (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
    {a b c : Nat} (hab : a ≠ b) (hcT : HasCherry a b T) (hcS : HasCherry a c S)
    {q r : RMAF.Vertex} (hcuts : (pendantOriginal S a b).Perm [q,r])
    (hql : subtreeLabels S q = [c]) {F : List (List Nat)}
    (hF : agreement T S F = true) {B : List Nat} (hB : B ∈ F)
    (ha : a ∈ B) (hcB : c ∉ B) (hb : [b] ∈ F)
    (hd : ∃ d, d ∈ B ∧ d ∈ subtreeLabels S r) :
    ∃ G, agreement T S G = true ∧ G.length = F.length ∧
      VertexGeometry.Refines G (literalThree S q r) := by
  have hBne : [b] ≠ B := by
    intro he
    have hh : a = b := by simpa [←he] using ha
    exact hab hh
  have hbb : [b] ∈ F.erase B := (List.mem_erase_of_ne hBne).2 hb
  let R := (F.erase B).erase [b]
  have perm : F.Perm (B :: [b] :: R) :=
    (List.perm_cons_erase hB).trans ((List.perm_cons_erase hbb).cons B)
  have hFg := agreement_perm T S F (B :: [b] :: R) perm hF
  obtain ⟨hG,hlen,hcov⟩ := actual_grouped_exchange hnT hnS hab hcT hcS hcuts hql B R hFg ha hcB hd
  refine ⟨_,hG,?_,hcov⟩
  exact hlen.trans perm.length_eq.symm
end Universal233.Rule4
