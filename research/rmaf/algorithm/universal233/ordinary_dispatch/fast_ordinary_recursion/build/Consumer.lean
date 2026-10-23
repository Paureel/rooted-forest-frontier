import Endpoints
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

theorem checked_nonempty {S : Tree} {Q : List (List Nat)}
 (hp : partitionCheck (leaves S) Q = true) {B : List Nat} (hb : B ∈ Q) : B ≠ [] := by
 have hall : Q.all (fun B => !B.isEmpty) = true := by
   simp only [partitionCheck,Bool.and_eq_true] at hp
   exact hp.1.1
 have hh := List.all_eq_true.1 hall B hb
 intro he; simp [he] at hh

theorem checked_nodup {S : Tree} {Q : List (List Nat)}
 (hp : partitionCheck (leaves S) Q = true) (he : pairwiseEmbeddings S Q = true) : Q.Nodup := by
 apply List.Pairwise.imp_of_mem (p := (executable_pairwiseEmbeddings S Q).1 he)
 intro B C hB hC hc e
 subst C
 obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B (checked_nonempty hp hB)
 obtain ⟨v,hv⟩ := leaf_exists (block_labels hp hB hx)
 have hm := (minimalVertices_terminal B S v x hv).2 hx
 exact hc v ⟨(minimalVertices_correct B S v).1 hm,(minimalVertices_correct B S v).1 hm⟩

theorem refined_length {T S : Tree} {Q F : List (List Nat)}
 (hp : partitionCheck (leaves S) Q = true) (he : pairwiseEmbeddings S Q = true)
 (ha : agreement T S F = true) (href : Refines F Q) : Q.length ≤ F.length := by
 classical
 have exists_pick : ∀ U, U ∈ Q → ∃ B, B ∈ F ∧ ∃ x, x ∈ U ∧ x ∈ B := by
   intro U hU
   obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil U (checked_nonempty hp hU)
   obtain ⟨B,hB,hxB⟩ := partitionCheck_covers _ F (source_agreement_checks ha).1 x (block_labels hp hU hx)
   exact ⟨B,hB,x,hx,hxB⟩
 let pick : List Nat → List Nat := fun U =>
   if h : ∃ B, B ∈ F ∧ ∃ x, x ∈ U ∧ x ∈ B then Classical.choose h else []
 have spec : ∀ U, U ∈ Q → pick U ∈ F ∧ ∃ x, x ∈ U ∧ x ∈ pick U := by
   intro U hU
   have hh := exists_pick U hU
   simp only [pick,dif_pos hh]
   exact Classical.choose_spec hh
 have same : ∀ U V, U ∈ Q → V ∈ Q → pick U = pick V → U = V := by
   intro U V hU hV e
   obtain ⟨hB,x,hxU,hxB⟩ := spec U hU
   obtain ⟨hC,y,hyV,hyC⟩ := spec V hV
   obtain ⟨W,hW,hBW⟩ := href (pick U) hB
   have hyB : y ∈ pick U := e.symm ▸ hyC
   obtain ⟨u,hu⟩ := leaf_exists (block_labels hp hU hxU)
   obtain ⟨v,hv⟩ := leaf_exists (block_labels hp hV hyV)
   have eU := checked_support_unique S Q he U W hU hW u
     ((minimalVertices_terminal U S u x hu).2 hxU)
     ((minimalVertices_terminal W S u x hu).2 (hBW x hxB))
   have eV := checked_support_unique S Q he V W hV hW v
     ((minimalVertices_terminal V S v y hv).2 hyV)
     ((minimalVertices_terminal W S v y hv).2 (hBW y hyB))
   exact eU.trans eV.symm
 have nd : (Q.map pick).Nodup := by
   change (Q.map pick).Pairwise (fun x y => x ≠ y)
   rw [List.pairwise_map]
   apply List.Pairwise.imp_of_mem (p := checked_nodup hp he)
   intro U V hU hV hne ee
   exact hne (same U V hU hV ee)
 have sub : Q.map pick ⊆ F := by
   intro B hb
   obtain ⟨U,hU,rfl⟩ := List.mem_map.1 hb
   exact (spec U hU).1
 simpa using nd.length_le_of_subset sub

theorem materialization_exists {S : Tree} {B : List Nat} {x : Nat}
 (hx : x ∈ leaves S) (hB : x ∈ B) : ∃ s, restrict B S = some s := by
 have hf : x ∈ (leaves S).filter B.contains := by simp [hx,hB]
 cases hr : restrict B S with
 | some s => exact ⟨s,rfl⟩
 | none =>
   have hh := restrict_leaf_filter B S
   rw [hr] at hh
   cases hem : ((leaves S).filter B.contains).isEmpty with
   | false => simp [hem] at hh
   | true => have he : (leaves S).filter B.contains = [] := List.isEmpty_iff.1 hem
             rw [he] at hf; exact False.elim (List.not_mem_nil hf)

theorem forest_length {S : Tree} {Q : List (List Nat)}
 (hp : partitionCheck (leaves S) Q = true) :
 (makeChild S Q (Q.length-1)).sourceForest.length = Q.length := by
 have all : ∀ B, B ∈ Q → ∃ s, restrict B S = some s := by
   intro B hB
   obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B (checked_nonempty hp hB)
   exact materialization_exists (block_labels hp hB hx) hx
 have loop : ∀ Q : List (List Nat), (∀ B, B ∈ Q → ∃ s, restrict B S = some s) →
     (Q.filterMap (fun B => restrict B S)).length = Q.length := by
   intro Q
   induction Q with
   | nil => intro _; rfl
   | cons B Q ih =>
     intro all
     obtain ⟨s,hs⟩ := all B (by simp)
     simpa [hs] using congrArg Nat.succ (ih (fun C hc => all C (by simp [hc])))
 exact loop Q all

/-- Paid costs telescope in the ORIGINAL objective, under the actual source
checks. There is no uncharged display-edge union or assumed size inequality. -/
theorem paid_budget_identity {T S : Tree} {c : Child} {F : List (List Nat)}
 (hp : partitionCheck (leaves S) c.partition = true)
 (he : pairwiseEmbeddings S c.partition = true)
 (paid : c.paid+1 = c.partition.length) (hf : feasible T S c F) :
 c.paid + (F.length-c.partition.length) = F.length-1 := by
 have hlen := refined_length hp he hf.1 hf.2
 omega

/-- If each of the THREE literal high-branch children is solved exactly, a
minimum among their returned original agreements is the original minimum.
This is conditional on child-specific IH and proves no recursive solver. -/
theorem ordinary_minimum {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hn : (leaves S).Nodup) (hc : CherryAt T p a b)
 (solve : Child → List (List Nat))
 (ih : ∀ c, c ∈ branches S a b → ExactChild T S c (solve c))
 (best : List (List Nat))
 (chosen : ∃ c, c ∈ branches S a b ∧ best = solve c)
 (least : ∀ c, c ∈ branches S a b → best.length ≤ (solve c).length) :
 agreement T S best = true ∧ ∀ F, agreement T S F = true → best.length ≤ F.length := by
 obtain ⟨c,hc',rfl⟩ := chosen
 refine ⟨(ih c hc').1.1,?_⟩
 intro F ha
 obtain ⟨d,hd,hf⟩ := ordinary_branches_cover hn ha hc
 exact Nat.le_trans (least d hd) ((ih d hd).2 F hf)
end Universal233.CherryBranching
