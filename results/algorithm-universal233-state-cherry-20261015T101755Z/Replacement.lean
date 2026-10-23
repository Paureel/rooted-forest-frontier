import Endpoint

namespace ForestState
open RMAF RestrictionBridge

theorem checked_unique_block (L : List Nat) (F : List (List Nat))
    (hp : partitionCheck L F = true) (A B : List Nat) (hA : A ∈ F) (hB : B ∈ F)
    (x : Nat) (hxA : x ∈ A) (hxB : x ∈ B) : A = B := by
  obtain ⟨U,hU,hxU,hc,unique⟩ := unique_label_owner F x
    (checked_count L F hp (checked_label L F hp hA hxA))
  exact (unique A hA hxA).trans (unique B hB hxB).symm

theorem checked_forest_nodup (L : List Nat) (F : List (List Nat))
    (hp : partitionCheck L F = true) : F.Nodup := by
  apply List.nodup_iff_count.2
  intro B
  by_cases hB : B ∈ F
  · obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B (checked_nonempty L F hp B hB)
    obtain ⟨U,hU,hxU,hc,unique⟩ := unique_label_owner F x
      (checked_count L F hp (checked_label L F hp hB hx))
    have he := unique B hB hx
    rw [he,hc]
    omega
  · rw [List.count_eq_zero.2 hB]
    omega

theorem source_label_owner (ss : List Tree) (x : Nat)
    (hc : (ss.map leaves).flatten.count x = 1)
    (s u : Tree) (hs : s ∈ ss) (hu : u ∈ ss)
    (hxs : x ∈ leaves s) (hxu : x ∈ leaves u) : s = u := by
  induction ss with
  | nil => simp at hs
  | cons v vs ih =>
    simp only [List.map_cons,List.flatten_cons,List.count_append] at hc
    rcases List.mem_cons.1 hs with he | hst
    · subst s
      rcases List.mem_cons.1 hu with he | hut
      · exact he.symm
      · have hpos := List.count_pos_iff.2 hxs
        have hp := List.count_pos_iff.2 (List.mem_flatten.2
          ⟨leaves u,List.mem_map.2 ⟨u,hut,rfl⟩,hxu⟩)
        omega
    · rcases List.mem_cons.1 hu with he | hut
      · subst u
        have hpos := List.count_pos_iff.2 hxu
        have hp := List.count_pos_iff.2 (List.mem_flatten.2
          ⟨leaves s,List.mem_map.2 ⟨s,hst,rfl⟩,hxs⟩)
        omega
      · have hn : x ∉ leaves v := by
          intro hxv
          have hpos := List.count_pos_iff.2 hxv
          have hp := List.count_pos_iff.2 (List.mem_flatten.2
            ⟨leaves s,List.mem_map.2 ⟨s,hst,rfl⟩,hxs⟩)
          omega
        exact ih (by simpa [List.count_eq_zero.2 hn] using hc) hst hut

theorem proper_source_owner (T : Option Tree) (ss : List Tree)
    (hp : proper T ss = true) (s u : Tree) (hs : s ∈ ss) (hu : u ∈ ss)
    (x : Nat) (hxs : x ∈ leaves s) (hxu : x ∈ leaves u) : s = u := by
  have hQ := (proper_parts T ss hp).2
  have hx := checked_label (labels T) (ss.map leaves) hQ
    (List.mem_map.2 ⟨s,hs,rfl⟩) hxs
  exact source_label_owner ss x (checked_count (labels T) (ss.map leaves) hQ hx)
    s u hs hu hxs hxu

theorem proper_source_nodup (T : Option Tree) (ss : List Tree)
    (hp : proper T ss = true) (s : Tree) (hs : s ∈ ss) : (leaves s).Nodup := by
  exact checked_block_nodup (labels T) (ss.map leaves) (proper_parts T ss hp).2
    (leaves s) (List.mem_map.2 ⟨s,hs,rfl⟩)

theorem pairwise_of_distinct (t : Tree) (F : List (List Nat)) (nd : F.Nodup)
    (h : ∀ A ∈ F, ∀ B ∈ F, A ≠ B →
      disjointVertices (minimalVertices A t) (minimalVertices B t) = true) :
    pairwiseEmbeddings t F = true := by
  induction F with
  | nil => rfl
  | cons A F ih =>
    have hn := List.nodup_cons.1 nd
    simp only [pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true]
    refine ⟨?_,ih hn.2 ?_⟩
    · intro B hB
      exact h A (by simp) B (by simp [hB]) (by intro he; subst B; exact hn.1 hB)
    · intro B hB C hC hne
      exact h B (by simp [hB]) C (by simp [hC]) hne

theorem source_family_partition (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (hp : proper T ss = true) (hF : partitionCheck (labels T) F = true)
    (href : ∀ B ∈ F, ∃ s ∈ ss, B ⊆ leaves s) (s : Tree) (hs : s ∈ ss) :
    partitionCheck (leaves s) (family (leaves s) F) = true := by
  have hQ := (proper_parts T ss hp).2
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB
    have hn := checked_nonempty (labels T) F hF B ((mem_family _ _ _).1 hB).1
    simpa using hn
  · intro x hx
    have hxl := checked_label (labels T) (ss.map leaves) hQ (List.mem_map.2 ⟨s,hs,rfl⟩) hx
    have own : ∀ B ∈ F, x ∈ B → B ⊆ leaves s := by
      intro B hB hxB
      obtain ⟨u,hu,hBu⟩ := href B hB
      have he := proper_source_owner T ss hp u s hu hs x (hBu hxB) hx
      simpa [he] using hBu
    apply beq_iff_eq.2
    rw [count_family_flatten F (leaves s) x own,checked_count (labels T) F hF hxl]
  · intro x hx
    obtain ⟨B,hB,hxB⟩ := List.mem_flatten.1 hx
    exact List.contains_iff_mem.2 (((mem_family _ _ _).1 hB).2 hxB)

theorem agrees_from_checks (t : Tree) (ss : List Tree) (F : List (List Nat))
    (hp : proper (some t) ss = true) (hF : partitionCheck (leaves t) F = true)
    (href : ∀ B ∈ F, ∃ s ∈ ss, B ⊆ leaves s)
    (ht : pairwiseEmbeddings t F = true)
    (top : ∀ s ∈ ss, ∀ B ∈ F, B ⊆ leaves s → restrictionAgrees t s B = true)
    (emb : ∀ s ∈ ss, ∀ A ∈ F, ∀ B ∈ F, A ⊆ leaves s → B ⊆ leaves s → A ≠ B →
      disjointVertices (minimalVertices A s) (minimalVertices B s) = true) :
    agrees (some t) ss F = true := by
  simp only [agrees,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,contained_iff]
  refine ⟨⟨⟨⟨hp,hF⟩,href⟩,ht⟩,?_⟩
  intro s hs
  simp only [sourceCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨source_family_partition (some t) ss F hp hF href s hs,?_⟩,?_⟩
  · intro B hB
    exact top s hs B ((mem_family _ _ _).1 hB).1 ((mem_family _ _ _).1 hB).2
  · apply pairwise_of_distinct s _
    · exact List.Sublist.nodup (List.filter_sublist) (checked_forest_nodup (leaves t) F hF)
    · intro A hA B hB hne
      have aa := (mem_family _ _ _).1 hA
      have bb := (mem_family _ _ _).1 hB
      exact emb s hs A aa.1 B bb.1 aa.2 bb.2 hne

def reassignedForest (F : List (List Nat)) (A : List Nat) (b : Nat) :=
  (b :: A) :: ((F.erase A).erase [b])

theorem reassignment_partition (L : List Nat) (F : List (List Nat)) (A : List Nat) (b : Nat)
    (hp : partitionCheck L F = true) (hA : A ∈ F) (hs : [b] ∈ F) (hb : b ∉ A) :
    partitionCheck L (reassignedForest F A b) = true := by
  have hne : [b] ≠ A := by intro he; rw [←he] at hb; simp at hb
  have hsr : [b] ∈ F.erase A := (List.mem_erase_of_ne hne).2 hs
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB
    rcases List.mem_cons.1 hB with he | hm
    · subst B; simp
    · have hn := checked_nonempty L F hp B (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      simpa using hn
  · intro x hx
    have hcA := flatten_count_erase F A hA x
    have hcs := flatten_count_erase (F.erase A) [b] hsr x
    have hc := checked_count L F hp hx
    apply beq_iff_eq.2
    simp only [reassignedForest,List.flatten_cons,List.count_append,List.count_cons]
    simp only [List.count_cons,List.count_nil,Nat.zero_add] at hcs
    cases he : (b == x) <;> simp_all
    all_goals omega
  · intro x hx
    obtain ⟨B,hB,hxB⟩ := List.mem_flatten.1 hx
    apply List.contains_iff_mem.2
    rcases List.mem_cons.1 hB with he | hm
    · subst B
      rcases List.mem_cons.1 hxB with he | hm
      · subst x; exact checked_label L F hp hs (by simp)
      · exact checked_label L F hp hA hm
    · exact checked_label L F hp (List.mem_of_mem_erase (List.mem_of_mem_erase hm)) hxB

theorem reassignment_remaining (L : List Nat) (F : List (List Nat)) (A : List Nat) (a b : Nat)
    (hp : partitionCheck L F = true) (hA : A ∈ F) (hs : [b] ∈ F) (ha : a ∈ A)
    (B : List Nat) (hB : B ∈ (F.erase A).erase [b]) :
    B ∈ F ∧ a ∉ B ∧ b ∉ B := by
  have nd := checked_forest_nodup L F hp
  have hm : B ∈ F := List.mem_of_mem_erase (List.mem_of_mem_erase hB)
  refine ⟨hm,?_,?_⟩
  · intro hx
    have he := checked_unique_block L F hp B A hm hA a hx ha
    subst B
    exact nd.not_mem_erase (List.mem_of_mem_erase hB)
  · intro hx
    have he := checked_unique_block L F hp B [b] hm hs b hx (by simp)
    subst B
    exact (nd.erase A).not_mem_erase hB

theorem agrees_block_topology (t : Tree) (ss : List Tree) (F : List (List Nat))
    (h : agrees (some t) ss F = true) (s : Tree) (hs : s ∈ ss)
    (B : List Nat) (hB : B ∈ F) (sub : B ⊆ leaves s) : restrictionAgrees t s B = true := by
  have sc := (agrees_parts (some t) ss F h).2.2.2.2 s hs
  have ho : (family (leaves s) F).all (targetAgrees (some t) s) = true := by
    simp only [sourceCheck,Bool.and_eq_true] at sc
    exact sc.1.2
  exact List.all_eq_true.1 ho B ((mem_family _ _ _).2 ⟨hB,sub⟩)

theorem agrees_block_source_clear (t : Tree) (ss : List Tree) (F : List (List Nat))
    (h : agrees (some t) ss F = true) (s : Tree) (hs : s ∈ ss)
    (A B : List Nat) (hA : A ∈ F) (hB : B ∈ F)
    (subA : A ⊆ leaves s) (subB : B ⊆ leaves s) (hne : A ≠ B) :
    disjointVertices (minimalVertices A s) (minimalVertices B s) = true := by
  have sc := (agrees_parts (some t) ss F h).2.2.2.2 s hs
  have ho : pairwiseEmbeddings s (family (leaves s) F) = true := by
    simp only [sourceCheck,Bool.and_eq_true] at sc
    exact sc.2
  exact pairwise_distinct_members s (family (leaves s) F) ho A B
    ((mem_family _ _ _).2 ⟨hA,subA⟩) ((mem_family _ _ _).2 ⟨hB,subB⟩) hne

theorem reassignment_preserves_agreement (t : Tree) (ss : List Tree) (F : List (List Nat))
    (a b : Nat) (A : List Nat) (h : agrees (some t) ss F = true)
    (ch : cherry a b t = true) (s0 : Tree) (hs0 : s0 ∈ ss) (chs : cherry a b s0 = true)
    (hA : A ∈ F) (hsingle : [b] ∈ F) (ha : a ∈ A) (hb : b ∉ A) :
    agrees (some t) ss (reassignedForest F A b) = true := by
  obtain ⟨hp,hF,href,ht,hs⟩ := agrees_parts (some t) ss F h
  have ndt := (proper_parts (some t) ss hp).1
  obtain ⟨w,hw⟩ := cherry_at_exists s0 a b chs
  obtain ⟨sA,hsA,subA⟩ := href A hA
  have esA := proper_source_owner (some t) ss hp sA s0 hsA hs0 a (subA ha) hw.labels.1
  have subA0 : A ⊆ leaves s0 := by simpa [esA] using subA
  have new_owner : ∀ s ∈ ss, (b :: A) ⊆ leaves s → s = s0 := by
    intro s hss sub
    exact proper_source_owner (some t) ss hp s s0 hss hs0 a (sub (by simp [ha])) hw.labels.1
  have remaining := reassignment_remaining (leaves t) F A a b hF hA hsingle ha
  have hnewF := reassignment_partition (leaves t) F A b hF hA hsingle hb
  have targetclear : ∀ C ∈ (F.erase A).erase [b],
      disjointVertices (minimalVertices (b :: A) t) (minimalVertices C t) = true := by
    intro C hC
    have rc := remaining C hC
    have hne : A ≠ C := by intro he; rw [←he] at rc; exact rc.2.1 ha
    exact endpoint_reassignment_embeddings t A C a b ndt ch ha hb rc.2.1 rc.2.2
      (pairwise_distinct_members t F ht A C hA rc.1 hne)
  apply agrees_from_checks t ss _ hp hnewF
  · intro B hB
    rcases List.mem_cons.1 hB with he | hm
    · subst B
      refine ⟨s0,hs0,?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with he | hm
      · subst x; exact hw.labels.2
      · exact subA0 hm
    · exact href B (remaining B hm).1
  · simp only [reassignedForest,pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true]
    exact ⟨targetclear,pairwise_erase t (F.erase A) [b] (pairwise_erase t F A ht)⟩
  · intro s hss B hB sub
    rcases List.mem_cons.1 hB with he | hm
    · subst B
      have he := new_owner s hss sub
      subst s
      exact synchronized_endpoint_reassignment_topology t s0 a b A ndt
        (proper_source_nodup (some t) ss hp s0 hs0) ch chs ha hb
        (agrees_block_topology t ss F h s0 hs0 A hA subA0)
    · exact agrees_block_topology t ss F h s hss B (remaining B hm).1 sub
  · intro s hss B hB C hC subB subC hne
    rcases List.mem_cons.1 hB with eB | rB
    · subst B
      have he := new_owner s hss subB
      subst s
      have rC : C ∈ (F.erase A).erase [b] :=
        (List.mem_cons.1 hC).resolve_left (Ne.symm hne)
      have rc := remaining C rC
      have hAC : A ≠ C := by intro he; rw [←he] at rc; exact rc.2.1 ha
      exact endpoint_reassignment_embeddings s0 A C a b
        (proper_source_nodup (some t) ss hp s0 hs0) chs ha hb rc.2.1 rc.2.2
        (agrees_block_source_clear t ss F h s0 hs0 A C hA rc.1 subA0 subC hAC)
    · rcases List.mem_cons.1 hC with eC | rC
      · subst C
        have he := new_owner s hss subC
        subst s
        have rb := remaining B rB
        have hAB : A ≠ B := by intro he; rw [←he] at rb; exact rb.2.1 ha
        apply (disjoint_symmetry _ _).2
        exact endpoint_reassignment_embeddings s0 A B a b
          (proper_source_nodup (some t) ss hp s0 hs0) chs ha hb rb.2.1 rb.2.2
          (agrees_block_source_clear t ss F h s0 hs0 A B hA rb.1 subA0 subB hAB)
      · exact agrees_block_source_clear t ss F h s hss B C
          (remaining B rB).1 (remaining C rC).1 subB subC hne

theorem reassignment_length (L : List Nat) (F : List (List Nat)) (A : List Nat) (b : Nat)
    (hF : partitionCheck L F = true) (hA : A ∈ F) (hs : [b] ∈ F) (hb : b ∉ A) :
    (reassignedForest F A b).length + 1 = F.length := by
  have hne : [b] ≠ A := by intro he; rw [←he] at hb; simp at hb
  have hsr : [b] ∈ F.erase A := (List.mem_erase_of_ne hne).2 hs
  have hp := List.length_pos_iff.2 (List.ne_nil_of_mem hsr)
  have hq := List.length_pos_iff.2 (List.ne_nil_of_mem hA)
  simp only [reassignedForest,List.length_cons,List.length_erase_of_mem hsr,
    List.length_erase_of_mem hA]
  have he := List.length_erase_of_mem hA
  omega

theorem CherryAt.to_cherry {t : Tree} {a b : Nat} {w : Vertex} (h : CherryAt a b t w) :
    cherry a b t = true := by
  induction h with
  | straight => simp [cherry]
  | swapped => simp [cherry]
  | left h ih => simp [cherry,ih]
  | right h ih => simp [cherry,ih]

theorem common_cherry_no_larger (t : Tree) (ss : List Tree) (F : List (List Nat))
    (a b : Nat) (h : agrees (some t) ss F = true) (ch : cherry a b t = true)
    (source : ∃ s ∈ ss, cherry a b s = true) :
    ∃ G, agrees (some t) ss G = true ∧ G.length ≤ F.length ∧
      ∃ B ∈ G, a ∈ B ∧ b ∈ B := by
  have hp := agrees_parts (some t) ss F h
  obtain ⟨w,hw⟩ := cherry_at_exists t a b ch
  obtain ⟨A,hA,ha⟩ := checked_covers (leaves t) F hp.2.1 hw.labels.1
  by_cases hb : b ∈ A
  · exact ⟨F,h,Nat.le_refl _,A,hA,ha,hb⟩
  · obtain ⟨B,hB,hbB⟩ := checked_covers (leaves t) F hp.2.1 hw.labels.2
    have haB : a ∉ B := by
      intro hm
      have he := checked_unique_block (leaves t) F hp.2.1 A B hA hB a ha hm
      exact hb (he.symm ▸ hbB)
    obtain ⟨s,hs,chs⟩ := source
    rcases actual_separated_cherry_singleton t ss F a b h ch A B hA hB ha hbB hb haB with ea | eb
    · subst A
      have ch' := hw.symm.to_cherry
      obtain ⟨v,hv⟩ := cherry_at_exists s a b chs
      have hs' := hv.symm.to_cherry
      have hg := reassignment_preserves_agreement t ss F b a B h ch' s hs hs' hB hA hbB haB
      have hl := reassignment_length (leaves t) F B a hp.2.1 hB hA haB
      refine ⟨reassignedForest F B a,hg,by omega,a :: B,by simp [reassignedForest],?_,?_⟩
      · simp
      · simp [hbB]
    · subst B
      have hg := reassignment_preserves_agreement t ss F a b A h ch s hs chs hA hB ha hb
      have hl := reassignment_length (leaves t) F A b hp.2.1 hA hB hb
      refine ⟨reassignedForest F A b,hg,by omega,b :: A,by simp [reassignedForest],?_,?_⟩
      · simp [ha]
      · simp

end ForestState
