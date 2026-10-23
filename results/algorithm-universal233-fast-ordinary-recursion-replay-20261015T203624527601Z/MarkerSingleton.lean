import Deletion
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge VertexGeometry

theorem restrict_singleton (t : Tree) (y : Nat) (nd : (leaves t).Nodup)
    (hy : y∈leaves t) : restrict [y] t=some (.leaf y) := by
  obtain ⟨u,hu⟩ := restriction_exists t [y] ⟨y,hy,by simp⟩
  have hl : leaves u=[y] := ForestState.subset_singleton_eq (leaves u) y
    (leaves_nonempty u)
    (fun _ hx => ((restricted_labels_exact t u [y] hu).1 hx).2)
    (restricted_nodup t u [y] hu nd)
  exact hu.trans (congrArg some (ForestState.tree_of_singleton_leaves u y hl))

theorem singleton_minimal_selected (t : Tree) (y : Nat) (nd : (leaves t).Nodup)
    (v : RMAF.Vertex) (hv : v∈minimalVertices [y] t) : selectedLeaves [y] t v := by
  obtain ⟨a,b,ha,hb,hp⟩ := (minimalVertices_correct [y] t v).1 hv
  have hab := singleton_selected_address_unique t y nd a b ha hb
  subst b
  have hva := path_identical v a hp
  simpa [hva] using ha

theorem singleton_clear (t : Tree) (y : Nat) (B : List Nat)
    (nd : (leaves t).Nodup) (hn : y∉B) :
    Clear (minimalVertices [y] t) (minimalVertices B t) := by
  intro v hv hw
  have hs := singleton_minimal_selected t y nd v hv
  exact (disjoint_parent_overlap_nonlabel [y] B t v
    (by
      intro x hx hxB
      have hxy : x=y := by simpa using hx
      subst x
      exact hn hxB) hv hw).1 hs

theorem partition_add_singleton (X : List Nat) (y : Nat) (F : List (List Nat))
    (hn : y∉X) (hp : partitionCheck X F=true) : partitionCheck (y::X) ([y]::F)=true := by
  have ny : y∉F.flatten := fun h =>
    hn (Universal233.SourceCoverage.partitionCheck_subset X F hp h)
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · simp
    · have hne := checked_nonempty X F hp B hB
      cases B <;> simp_all
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · simp [List.count_eq_zero.2 ny]
    · have hxy : y≠x := by intro h;subst x;exact hn hx
      simp [hxy,checked_count X F hp hx]
  · intro x hx
    apply List.contains_iff_mem.2
    simp only [List.flatten_cons,List.mem_append,List.mem_singleton] at hx
    rcases hx with rfl | hx
    · simp
    · exact List.mem_cons_of_mem y
        (Universal233.SourceCoverage.partitionCheck_subset X F hp hx)

/-- A marker can always be retained as a singleton component, paying exactly
one additional ordinary cut. Local embeddings are lifted to the actual marked
input, and the new singleton is checked against every lifted span. -/
theorem singleton_extension (T S t s : Tree) (X : List Nat) (y : Nat)
    (ndT : (leaves T).Nodup) (ndS : (leaves S).Nodup) (hn : y∉X)
    (lt : (leaves T).Perm (y::X)) (ls : (leaves S).Perm (y::X))
    (lrt : (leaves t).Perm X) (lrs : (leaves s).Perm X)
    (ht : restrict X T=some t) (hs : restrict X S=some s)
    (F : List (List Nat)) (ha : agreement t s F=true) :
    agreement T S ([y]::F)=true := by
  have hh := ha
  simp only [agreement,Bool.and_eq_true] at hh
  have pX := (partition_labels_congr (leaves t) X F (fun _ => lrt.mem_iff)).1 hh.1.1.1.1
  have sub : ∀ B∈F, B⊆X := fun B hB _ hx =>
    checked_label X F pX hB hx
  have heT : pairwiseEmbeddings T F=true :=
    (pairwise_transport T t X F ht sub).2 hh.1.2
  have heS : pairwiseEmbeddings S F=true :=
    (pairwise_transport S s X F hs sub).2 hh.2
  have hpart := partition_add_singleton X y F hn pX
  have hyT : y∈leaves T := lt.mem_iff.2 (by simp)
  have hyS : y∈leaves S := ls.mem_iff.2 (by simp)
  simp only [agreement,Bool.and_eq_true]
  refine ⟨⟨⟨⟨(partition_labels_congr (leaves T) (y::X) ([y]::F)
      (fun _ => lt.mem_iff)).2 hpart,
    (partition_labels_congr (leaves S) (y::X) ([y]::F)
      (fun _ => ls.mem_iff)).2 hpart⟩,?_⟩,?_⟩,?_⟩
  · simp only [List.all_cons,Bool.and_eq_true]
    constructor
    · simp [restrictionAgrees,restrict_singleton T y ndT hyT,restrict_singleton S y ndS hyS,sameShape]
    · apply List.all_eq_true.2
      intro B hB
      rw [←sameShape_restrict_inside T S t s X B ht hs (sub B hB)]
      exact List.all_eq_true.1 hh.1.1.2 B hB
  · change F.all (fun B => disjointVertices (minimalVertices [y] T) (minimalVertices B T)) &&
      pairwiseEmbeddings T F=true
    rw [Bool.and_eq_true]
    exact ⟨List.all_eq_true.2 (fun B hB => (clear_iff _ _).2
      (singleton_clear T y B ndT (fun hx => hn (sub B hB hx)))),heT⟩
  · change F.all (fun B => disjointVertices (minimalVertices [y] S) (minimalVertices B S)) &&
      pairwiseEmbeddings S F=true
    rw [Bool.and_eq_true]
    exact ⟨List.all_eq_true.2 (fun B hB => (clear_iff _ _).2
      (singleton_clear S y B ndS (fun hx => hn (sub B hB hx)))),heS⟩
end OrdinaryCommonSplit
