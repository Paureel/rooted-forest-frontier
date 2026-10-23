import ForestPretest01

namespace ForestPretest01
open RMAF RestrictionBridge ForestState

/-- Exactly finite compositions of inner-label and outer-block permutations.
No desired coverage, agreement or minimum field is present. -/
inductive ForestPerm : Forest → Forest → Prop where
  | nil : ForestPerm [] []
  | cons {A B : List Nat} {F G : Forest} : A.Perm B → ForestPerm F G → ForestPerm (A::F) (B::G)
  | outer {F G : Forest} : F.Perm G → ForestPerm F G
  | append {F G H I : Forest} : ForestPerm F G → ForestPerm H I → ForestPerm (F++H) (G++I)
  | trans {F G H : Forest} : ForestPerm F G → ForestPerm G H → ForestPerm F H

namespace ForestPerm

theorem refl (F : Forest) : ForestPerm F F := .outer (.refl F)
theorem symm {F G : Forest} (h : ForestPerm F G) : ForestPerm G F := by
  induction h with
  | nil => exact .nil
  | cons hp _ ih => exact .cons hp.symm ih
  | outer hp => exact .outer hp.symm
  | append _ _ ih ij => exact .append ih ij
  | trans _ _ ih ij => exact .trans ij ih

theorem length_eq {F G : Forest} (h : ForestPerm F G) : F.length = G.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | outer hp => exact hp.length_eq
  | append _ _ ih ij => simp [ih,ij]
  | trans _ _ ih ij => exact ih.trans ij

theorem flatten_perm {F G : Forest} (h : ForestPerm F G) : F.flatten.Perm G.flatten := by
  induction h with
  | nil => exact .refl []
  | cons hp _ ih => exact hp.append ih
  | outer hp => exact hp.flatten
  | append _ _ ih ij => simpa using ih.append ij
  | trans _ _ ih ij => exact ih.trans ij

theorem all_eq {F G : Forest} (h : ForestPerm F G) (p : List Nat → Bool)
    (invariant : ∀ A B, A.Perm B → p A = p B) : F.all p = G.all p := by
  induction h with
  | nil => rfl
  | cons hp _ ih => simp only [List.all_cons,invariant _ _ hp,ih]
  | outer hp => exact hp.all_eq
  | append _ _ ih ij => simp only [List.all_append,ih,ij]
  | trans _ _ ih ij => exact ih.trans ij

theorem filter {F G : Forest} (h : ForestPerm F G) (p : List Nat → Bool)
    (invariant : ∀ A B, A.Perm B → p A = p B) :
    ForestPerm (F.filter p) (G.filter p) := by
  induction h with
  | nil => exact .nil
  | @cons A B F G hp hh ih =>
    have he := invariant A B hp
    cases ha : p A <;> simp only [List.filter_cons,ha,←he]
    · exact ih
    · exact .cons hp ih
  | outer hp => exact .outer (hp.filter p)
  | append _ _ ih ij => simpa only [List.filter_append] using ih.append ij
  | trans _ _ ih ij => exact ih.trans ij

theorem members {F G : Forest} (h : ForestPerm F G) :
    ∀ A ∈ F, ∃ B ∈ G, A.Perm B := by
  induction h with
  | nil => simp
  | @cons A B F G hp hh ih =>
    intro U hU
    rcases List.mem_cons.1 hU with rfl | hU
    · exact ⟨B,by simp,hp⟩
    · obtain ⟨V,hV,hp⟩ := ih U hU
      exact ⟨V,by simp [hV],hp⟩
  | outer hp => intro A hA; exact ⟨A,hp.subset hA,.refl A⟩
  | append _ _ ih ij =>
    intro A hA
    rcases List.mem_append.1 hA with hA | hA
    · obtain ⟨B,hB,hp⟩ := ih A hA; exact ⟨B,by simp [hB],hp⟩
    · obtain ⟨B,hB,hp⟩ := ij A hA; exact ⟨B,by simp [hB],hp⟩
  | trans _ _ ih ij =>
    intro A hA
    obtain ⟨B,hB,hAB⟩ := ih A hA
    obtain ⟨C,hC,hBC⟩ := ij B hB
    exact ⟨C,hC,hAB.trans hBC⟩
end ForestPerm

theorem partition_perm (L : List Nat) (F G : Forest) (h : ForestPerm F G) :
    partitionCheck L F = partitionCheck L G := by
  have he := h.all_eq (fun B => !B.isEmpty) (by
    intro A B hp
    have hn : A.isEmpty = B.isEmpty := by cases A <;> cases B <;> simp_all
    rw [hn])
  have hf := h.flatten_perm
  simp only [partitionCheck,he,hf.all_eq]
  congr 2
  exact List.all_congr rfl (fun x => congrArg (fun n : Nat => n == 1) (hf.count_eq x))

theorem embeddings_outer (t : Tree) (F G : Forest) (h : F.Perm G) :
    pairwiseEmbeddings t F = pairwiseEmbeddings t G := by
  apply Bool.eq_iff_iff.2
  rw [pairwise_iff,pairwise_iff]
  exact h.pairwise_iff (fun hh => (clear_symm _ _).1 hh)

theorem embeddings_perm (t : Tree) (F G : Forest) (h : ForestPerm F G) :
    pairwiseEmbeddings t F = pairwiseEmbeddings t G := by
  induction h with
  | nil => rfl
  | @cons A B F G hp hh ih =>
    simp only [pairwiseEmbeddings,ih]
    rw [Universal233.DepthOne.minimal_members t A B (fun _ => hp.mem_iff)]
    exact congrArg (fun b => b && pairwiseEmbeddings t G)
      (hh.all_eq (fun C => disjointVertices (minimalVertices B t) (minimalVertices C t))
      (fun C D hCD => by rw [Universal233.DepthOne.minimal_members t C D (fun _ => hCD.mem_iff)]))
  | outer hp => exact embeddings_outer t _ _ hp
  | @append F G H I hFG hHI ih ij =>
    have app (J K : Forest) : pairwiseEmbeddings t (J++K) =
      (pairwiseEmbeddings t J && pairwiseEmbeddings t K &&
        J.all (fun A => K.all (fun B => disjointVertices (minimalVertices A t) (minimalVertices B t)))) := by
      induction J with
      | nil => simp [pairwiseEmbeddings]
      | cons A J ih => simp [pairwiseEmbeddings,ih,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]
    rw [app,app,ih,ij]
    congr 1
    rw [hFG.all_eq _ (fun A B hAB => by rw [Universal233.DepthOne.minimal_members t A B (fun _ => hAB.mem_iff)])]
    apply List.all_congr rfl
    intro A
    exact hHI.all_eq _ (fun B C hBC => by rw [Universal233.DepthOne.minimal_members t B C (fun _ => hBC.mem_iff)])
  | trans _ _ ih ij => exact ih.trans ij

theorem targetAgrees_perm (T : Option Tree) (s : Tree) (A B : List Nat) (h : A.Perm B) :
    targetAgrees T s A = targetAgrees T s B := by
  cases T with
  | none => rfl
  | some t => simp only [targetAgrees,restrictionAgrees,
      Universal233.DepthOne.restrict_members t A B (fun _ => h.mem_iff),
      Universal233.DepthOne.restrict_members s A B (fun _ => h.mem_iff)]

theorem agrees_perm (T : Option Tree) (ss : List Tree) (F G : Forest) (h : ForestPerm F G) :
    agrees T ss F = agrees T ss G := by
  have hf (s : Tree) : ForestPerm (family (leaves s) F) (family (leaves s) G) :=
    h.filter _ (fun A B hp => hp.all_eq)
  have source (s : Tree) : sourceCheck T F s = sourceCheck T G s := by
    simp only [sourceCheck,partition_perm _ _ _ (hf s),embeddings_perm _ _ _ (hf s)]
    rw [(hf s).all_eq _ (targetAgrees_perm T s)]
  have target : targetEmbeddings T F = targetEmbeddings T G := by
    cases T with
    | none =>
      have hl := h.length_eq
      cases F <;> cases G <;> simp_all [targetEmbeddings]
    | some t => exact embeddings_perm t F G h
  simp only [agrees,partition_perm _ _ _ h,target]
  rw [h.all_eq _ (fun A B hp => by
    apply List.any_congr rfl
    intro s
    exact hp.all_eq)]
  congr 1
  exact List.all_congr rfl source

end ForestPretest01
