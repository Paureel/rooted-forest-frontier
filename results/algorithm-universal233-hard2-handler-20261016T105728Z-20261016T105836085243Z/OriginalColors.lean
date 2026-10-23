import WholeColors

namespace Universal233.WholeSourceMass
open RMAF VertexGeometry SourceCoverage

def jointLabel (T : Tree) (v w : RMAF.Vertex) (x : Nat) : Nat :=
  4 * colorLabel T v x + colorLabel T w x

theorem colorLabel_le_three (T : Tree) (v : RMAF.Vertex) (x : Nat) :
    colorLabel T v x ≤ 3 := region_le_three _ _

theorem jointCode_injective {a b c d : Nat} (hb : b ≤ 3) (hd : d ≤ 3)
    (he : 4*a+b = 4*c+d) : a = c ∧ b = d := by omega

theorem original_colors_members (D : List Nat) (T : Tree) (v : RMAF.Vertex)
    (hn : (leaves T).Nodup) (hs : ∀ x, x ∈ D → x ∈ leaves T)
    (hnv : ¬selectedLeaves D T v) (i : Nat) :
    i ∈ localColors D (colorLabel T v) ↔ i ∈ regions D T v := by
  rw [mem_localColors,regionList_mem]
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨a,ha⟩ := (singleton_selected_exists T x).mpr (hs x hx)
    have hDa := (selected_decompose_label D T a).mpr ⟨x,hx,ha⟩
    have he := colorLabel_at_address T v x hn a ha
    refine ⟨?_,⟨a,hDa,he.symm⟩⟩
    rw [he]
    exact nonlabel_region_lt_three v a (by intro e; subst a; exact hnv hDa)
  · rintro ⟨hi,a,ha,he⟩
    obtain ⟨x,hx,hxa⟩ := (selected_decompose_label D T a).mp ha
    exact ⟨x,hx,(colorLabel_at_address T v x hn a hxa).trans he⟩

/-- Exact occupied original-label count; root and empty-region cases are literal. -/
theorem original_colors_cardinality (D : List Nat) (T : Tree) (v : RMAF.Vertex)
    (hn : (leaves T).Nodup) (hs : ∀ x, x ∈ D → x ∈ leaves T)
    (hnv : ¬selectedLeaves D T v) :
    (localColors D (colorLabel T v)).length = (regions D T v).length := by
  apply same_members_length _ _ (localColors_nodup _ _) _
    (original_colors_members D T v hn hs hnv)
  exact List.Pairwise.filter _ (by decide : ([0,1,2] : List Nat).Nodup)

theorem original_colors_at_least_two (D : List Nat) (T : Tree) (v : RMAF.Vertex)
    (hn : (leaves T).Nodup) (hs : ∀ x, x ∈ D → x ∈ leaves T)
    (hnv : ¬selectedLeaves D T v) (hv : v ∈ minimalVertices D T) :
    2 ≤ (localColors D (colorLabel T v)).length := by
  rw [original_colors_cardinality D T v hn hs hnv]
  rcases executable_region_count_two_or_three D T v hnv hv with h | h <;> omega

theorem original_root_colors_exactly_two (D : List Nat) (T : Tree)
    (hn : (leaves T).Nodup) (hs : ∀ x, x ∈ D → x ∈ leaves T)
    (hnv : ¬selectedLeaves D T []) (hv : [] ∈ minimalVertices D T) :
    (localColors D (colorLabel T [])).length = 2 := by
  rw [original_colors_cardinality D T [] hn hs hnv]
  exact executable_root_region_count_two D T hnv hv

theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (L : List α) :
    L.eraseDups.Nodup := by
  cases L with
  | nil => simp
  | cons a as =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · simp [List.mem_eraseDups]
    · exact eraseDups_nodup (as.filter (fun b => !b == a))
termination_by L.length
decreasing_by
  have h := List.length_filter_le (fun b => !b == a) as
  simp only [List.length_cons]
  omega

theorem original_joint_members (D : List Nat) (T : Tree) (v w : RMAF.Vertex)
    (hn : (leaves T).Nodup) (hs : ∀ x, x ∈ D → x ∈ leaves T) (i : Nat) :
    i ∈ localColors D (jointLabel T v w) ↔
      i ∈ (jointColors D T v w).map (fun p => 4*p.1+p.2) := by
  simp only [mem_localColors,List.mem_map]
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨a,ha⟩ := (singleton_selected_exists T x).mpr (hs x hx)
    refine ⟨jointRegion v w a,(jointColors_mem D T v w _).mpr
      ⟨a,(selected_decompose_label D T a).mpr ⟨x,hx,ha⟩,rfl⟩,?_⟩
    simp [jointLabel,jointRegion,colorLabel_at_address T v x hn a ha,
      colorLabel_at_address T w x hn a ha]
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨a,ha,he⟩ := (jointColors_mem D T v w p).mp hp
    obtain ⟨x,hx,hxa⟩ := (selected_decompose_label D T a).mp ha
    refine ⟨x,hx,?_⟩
    rw [← he]
    simp [jointLabel,jointRegion,colorLabel_at_address T v x hn a hxa,
      colorLabel_at_address T w x hn a hxa]

/-- The base-four joint code preserves the cardinality of actual nonempty
original-label joint regions, including the count-two leafless-middle case. -/
theorem original_joint_cardinality (D : List Nat) (T : Tree) (v w : RMAF.Vertex)
    (hn : (leaves T).Nodup) (hs : ∀ x, x ∈ D → x ∈ leaves T) :
    (localColors D (jointLabel T v w)).length = (jointColors D T v w).length := by
  have hm : ((jointColors D T v w).map (fun p => 4*p.1+p.2)).Nodup := by
    apply nodup_map_of_injOn _ _ (eraseDups_nodup _)
    intro p hp q hq he
    obtain ⟨a,ha,hea⟩ := (jointColors_mem D T v w p).mp hp
    obtain ⟨b,hb,heb⟩ := (jointColors_mem D T v w q).mp hq
    have hp2 : p.2 ≤ 3 := by rw [← hea]; exact region_le_three w a
    have hq2 : q.2 ≤ 3 := by rw [← heb]; exact region_le_three w b
    obtain ⟨h1,h2⟩ := jointCode_injective hp2 hq2 he
    exact Prod.ext h1 h2
  have h := same_members_length _ _ (localColors_nodup _ _) hm
    (original_joint_members D T v w hn hs)
  simpa only [List.length_map] using h

theorem partition_target_support (S T : Tree) (A B C : List Nat)
    (hp : ParentPartition S A B C) (hs : ∀ x, x ∈ leaves S → x ∈ leaves T) :
    (∀ x, x ∈ A → x ∈ leaves T) ∧ (∀ x, x ∈ B → x ∈ leaves T) ∧
      (∀ x, x ∈ C → x ∈ leaves T) := by
  exact ⟨fun x hx => hs x ((hp.cover x).mpr (Or.inl hx)),
    fun x hx => hs x ((hp.cover x).mpr (Or.inr (Or.inl hx))),
    fun x hx => hs x ((hp.cover x).mpr (Or.inr (Or.inr hx)))⟩

end Universal233.WholeSourceMass
