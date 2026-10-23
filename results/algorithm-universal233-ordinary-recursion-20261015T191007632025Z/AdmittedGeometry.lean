import Attachment
namespace Universal233.Rule5Classification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local

theorem hasCherry_actual {T : Tree} {a b : Nat} (h : HasCherry a b T) :
 ∃ p, CherryAt T p a b ∨ CherryAt T p b a := by
 induction h with
 | here => exact ⟨[],Or.inl rfl⟩
 | swap => exact ⟨[],Or.inr rfl⟩
 | left _ ih =>
   obtain ⟨p,h | h⟩ := ih
   · exact ⟨false::p,Or.inl h⟩
   · exact ⟨false::p,Or.inr h⟩
 | right _ ih =>
   obtain ⟨p,h | h⟩ := ih
   · exact ⟨true::p,Or.inl h⟩
   · exact ⟨true::p,Or.inr h⟩

theorem earlierClear_cherry {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (h : earlierClear S T = true) (ch : CherryAt S p a b) : (cuts T a b).length = 2 := by
 have hc : (⟨p,a,b,cuts T a b⟩ : Candidate) ∈ candidates S T :=
   List.mem_map.2 ⟨(p,a,b),cherries_complete S p a b ch,rfl⟩
 exact beq_iff_eq.1 ((List.all_eq_true.1 h) _ hc)

theorem properPair_parts {T S : Tree} (h : properPair T S = true) :
 (leaves T).Nodup ∧ (leaves S).Nodup ∧ (∀ x, x ∈ leaves T ↔ x ∈ leaves S) := by
 simp only [properPair,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.contains_iff_mem] at h
 exact ⟨h.1.1.1,h.1.1.2,fun x => ⟨h.1.2 x,h.2 x⟩⟩

theorem admitted_parts {T S : Tree} {a b : Nat} (h : admitted T S a b = true) :
 properPair T S = true ∧ earlierClear T S = true ∧ earlierClear S T = true ∧
 pairwiseEmbeddings T (pendantPartition S a b) = true ∧ (cuts S a b).length = 2 := by
 simp only [admitted,Bool.and_eq_true,beq_iff_eq] at h
 exact ⟨h.1.1.1.1.1.1.1.1.1,h.1.1.1.1.1.1.1.2,h.1.1.1.1.1.1.2,h.1.1.2,h.1.1.1.2⟩

theorem restriction_good_pruned {T S : Tree} {X : List Nat} {p : RMAF.Vertex} {a b : Nat}
 (hn : (leaves T).Nodup) (hg : restrictionAgrees T S X = true)
 (ch : CherryAt S p a b) (ha : a ∈ X) (hb : b ∈ X) : PrunedCherry X a b T := by
 obtain ⟨V,hV,hcV⟩ := restrict_hasCherry (actual_hasCherry ch) X ha hb
 cases hU : restrict X T with
 | none => simp [restrictionAgrees,hV,hU] at hg
 | some U =>
   have hi : RootedIso U V := (sameShape_correct U V).1 (by simpa [restrictionAgrees,hV,hU] using hg)
   exact prunedCherry_of_restrict hn hU (iso_hasCherry (BinaryExchange.iso_symm hi) hcV)

/-- Actual no-earlier-rule guard in the reverse orientation supplies both
original target arcs. Agreement of X supplies the pruned cherry; the two
outside parts are deduced, rather than fields of a geometric certificate. -/
theorem guarded_good_cherry_attachment {T S : Tree} {X Y Z : List Nat}
 {p : RMAF.Vertex} {a b : Nat}
 (hn : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,Y,Z] = true)
 (he : pairwiseEmbeddings T [X,Y,Z] = true)
 (early : earlierClear S T = true) (good : restrictionAgrees T S X = true)
 (ch : CherryAt S p a b) (ha : a ∈ X) (hb : b ∈ X) :
 ∃ u v, cuts T a b = [u,v] ∧
 (((∀ x, x ∈ subtreeLabels T u ↔ x ∈ Y) ∧ (∀ x, x ∈ subtreeLabels T v ↔ x ∈ Z)) ∨
  ((∀ x, x ∈ subtreeLabels T u ↔ x ∈ Z) ∧ (∀ x, x ∈ subtreeLabels T v ↔ x ∈ Y))) ∧
 (∀ x, x ∈ coreLabels T a b ↔ x ∈ X) := by
 have h2 := earlierClear_cherry early ch
 have hc := List.eq_getElem_of_length_eq_two (cuts T a b) h2
 exact ⟨_,_,hc,actual_two_pendant_attachment hn hp he (restriction_good_pruned hn good ch ha hb) hc⟩

end Universal233.Rule5Classification
