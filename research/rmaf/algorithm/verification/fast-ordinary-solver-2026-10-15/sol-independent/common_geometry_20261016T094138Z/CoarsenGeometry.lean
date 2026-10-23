import CoarsenPartitionV2
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentGeometry

theorem block_fresh {z : Nat} {T : Tree} {F : List (List Nat)}
 (fresh : z∉leaves T) (hp : partitionCheck (leaves T) F=true) {B : List Nat} (hB : B∈F) : z∉B := by
 simp only [partitionCheck,Bool.and_eq_true] at hp
 intro hz
 exact fresh (List.contains_iff_mem.1 (List.all_eq_true.1 hp.2 z (List.mem_flatten.2 ⟨B,hB,hz⟩)))

theorem restrict_none_absent (T : Tree) (B : List Nat) (hn : restrict B T=none) :
 ∀x∈leaves T,x∉B := by
 induction T with
 | leaf y =>
  intro x hx
  have eq : x=y := by simpa [leaves] using hx
  subst x
  simpa [restrict] using hn
 | node l r il ir =>
  cases hl : restrict B l <;> cases hr : restrict B r <;> simp [restrict,hl,hr] at hn
  intro x hx
  rcases List.mem_append.1 hx with hx|hx
  · exact il hl x hx
  · exact ir hr x hx

theorem partition_block_nonnull {T : Tree} {F : List (List Nat)}
 (hp : partitionCheck (leaves T) F=true) {B : List Nat} (hB : B∈F) : restrict B T≠none := by
 have p := hp
 simp only [partitionCheck,Bool.and_eq_true] at p
 have bn : B≠[] := by
  have h := List.all_eq_true.1 p.1.1 B hB
  intro empty
  simp [empty] at h
 cases B with
 | nil => exact False.elim (bn rfl)
 | cons x xs =>
  have hx : x∈leaves T := List.contains_iff_mem.1
   (List.all_eq_true.1 p.2 x (List.mem_flatten.2 ⟨x::xs,hB,by simp⟩))
  intro none
  exact restrict_none_absent T (x::xs) none x hx (by simp)

theorem prune_restrictions_iso {T U : Tree} {B : List Nat}
 (h : restrictionAgrees T U B=true) (a b z : Nat) :
 MaybeIso (pruneOption a b z (restrict B T)) (pruneOption a b z (restrict B U)) := by
 unfold restrictionAgrees at h
 cases ht : restrict B T <;> cases hu : restrict B U <;> simp only [ht,hu] at h
 all_goals first | contradiction | exact prune_iso (same_iso h) a b z

theorem nonnull_iso_agrees {T U : Tree} {B : List Nat}
 (rel : MaybeIso (restrict B T) (restrict B U)) (nonnull : restrict B T≠none) :
 restrictionAgrees T U B=true := by
 generalize ht : restrict B T=t at rel nonnull
 generalize hu : restrict B U=u at rel
 unfold restrictionAgrees
 rw [ht,hu]
 cases rel with
 | none => exact False.elim (nonnull rfl)
 | some iso => exact iso_same iso

theorem disjoint_shrink {a b z : Nat} {C T : Tree} (gt : Grow a b z C T)
 (ab : a≠b) {B D : List Nat} (bz : z∉B) (dz : z∉D)
 (h : disjointVertices (minimalVertices B T) (minimalVertices D T)=true) :
 disjointVertices (minimalVertices (shrinkBlock a b z B) C)
   (minimalVertices (shrinkBlock a b z D) C)=true := by
 apply List.all_eq_true.2
 intro v hv
 cases hd : (minimalVertices (shrinkBlock a b z D) C).contains v with
 | false => rfl
 | true =>
  have pb := minimal_shrink_lift gt ab B bz v hv
  have pd := minimal_shrink_lift gt ab D dz v (List.contains_iff_mem.1 hd)
  have no := List.all_eq_true.1 h (embed a C T v) pb
  simp at no
  exact False.elim (no pd)

theorem pairwise_shrink {a b z : Nat} {C T : Tree} (gt : Grow a b z C T)
 (ab : a≠b) (F : List (List Nat)) (fresh : ∀B∈F,z∉B)
 (h : pairwiseEmbeddings T F=true) :
 pairwiseEmbeddings C (F.map (shrinkBlock a b z))=true := by
 induction F with
 | nil => rfl
 | cons B rest ih =>
  simp only [pairwiseEmbeddings,Bool.and_eq_true] at h
  simp only [List.map_cons,pairwiseEmbeddings,Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.2
    intro E hE
    obtain ⟨D,hD,rfl⟩ := List.mem_map.1 hE
    exact disjoint_shrink gt ab (fresh B (by simp)) (fresh D (by simp [hD]))
     (List.all_eq_true.1 h.1 D hD)
  · exact ih (fun D hD=>fresh D (by simp [hD])) h.2

theorem pairwise_filter (T : Tree) (F : List (List Nat)) (p : List Nat→Bool)
 (h : pairwiseEmbeddings T F=true) : pairwiseEmbeddings T (F.filter p)=true := by
 induction F with
 | nil => rfl
 | cons B rest ih =>
  simp only [pairwiseEmbeddings,Bool.and_eq_true] at h
  simp only [List.filter_cons]
  split
  · simp only [pairwiseEmbeddings,Bool.and_eq_true]
    refine ⟨?_,ih h.2⟩
    apply List.all_eq_true.2
    intro D hD
    exact List.all_eq_true.1 h.1 D (List.mem_filter.1 hD).1
  · exact ih h.2

theorem common_coarsening {a b z : Nat} {T U : Tree}
 (ht : HasCherry a b T) (hu : HasCherry a b U)
 (hp : DepthOne.proper T U=true) (fresh : z∉leaves T) (F : List (List Nat))
 (h : agreement T U F=true) :
 agreement (contract a b z T) (contract a b z U) (coarsen a b z F)=true ∧
 (coarsen a b z F).length≤F.length := by
 obtain ⟨nt,nu,perm⟩ := IndependentReconstruction.proper_parts hp
 have fu : z∉leaves U := fun hz=>fresh (perm.mem_iff.2 hz)
 have gt := actual_grow ht nt fresh
 have gu := actual_grow hu nu fu
 obtain ⟨rest,normal,_⟩ := IndependentCommon.contraction_normal ht z nt
 have ab : a≠b := by
  intro e
  exact (List.nodup_cons.1 (normal.nodup nt)).1 (by simp [e])
 simp only [agreement,Bool.and_eq_true] at h
 have pt := coarsen_partition ht nt fresh F h.1.1.1.1
 have pu := coarsen_partition hu nu fu F h.1.1.1.2
 have noZ : ∀B∈F,z∉B := fun B hB=>block_fresh fresh h.1.1.1.1 hB
 refine ⟨?_,coarsen_length F a b z⟩
 simp only [agreement,Bool.and_eq_true]
 refine ⟨⟨⟨⟨pt,pu⟩,?_⟩,
  pairwise_filter _ _ _ (pairwise_shrink gt ab F noZ h.1.2)⟩,
  pairwise_filter _ _ _ (pairwise_shrink gu ab F noZ h.2)⟩
 apply List.all_eq_true.2
 intro E hE
 have nonnull := partition_block_nonnull pt hE
 obtain ⟨mapped,_⟩ := List.mem_filter.1 hE
 obtain ⟨B,hB,rfl⟩ := List.mem_map.1 mapped
 have rel := prune_restrictions_iso (List.all_eq_true.1 h.1.1.2 B hB) a b z
 rw [←restrict_shrink gt ab B (noZ B hB),←restrict_shrink gu ab B (noZ B hB)] at rel
 exact nonnull_iso_agrees rel nonnull
end IndependentGeometry
