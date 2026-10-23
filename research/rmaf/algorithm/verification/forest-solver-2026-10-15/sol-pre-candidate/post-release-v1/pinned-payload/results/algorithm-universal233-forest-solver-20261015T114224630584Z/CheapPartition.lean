import BinaryEdge
namespace Universal233.BinaryCheap
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly RankDichotomy RankConsumer
abbrev SameMembers (K L : List Nat) := ∀ x, x ∈ K ↔ x ∈ L

theorem parent_cover (S : Tree) (A B C : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true) (x : Nat) :
    x ∈ leaves S ↔ x ∈ A ∨ x ∈ B ∨ x ∈ C := by
  simpa using partition_mem (leaves S) [A,B,C] hp x |>.symm

theorem class_values (S : Tree) (A B C D : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true) (x : Nat) (hx : x ∈ leaves S) :
    (cheapColor A B D x = 1 ↔ x ∈ ay A D) ∧
    (cheapColor A B D x = 4 ↔ x ∈ an A D) ∧
    (cheapColor A B D x = 0 ↔ x ∈ B) ∧
    (cheapColor A B D x = 2 ↔ x ∈ C) := by
  obtain ⟨hab,hac,hbc⟩ := Assembly.parent_partition_disjoint S A B C hp
  have hc := (parent_cover S A B C hp x).1 hx
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> by_cases hd : x ∈ D <;>
    simp_all [cheapColor,WholeSourceMass.taggedColor,sideColor,ay,an,yes,no]

def classes (A B C D : List Nat) := [ay A D,an A D,B,C]

theorem classes_nonempty (S : Tree) (A B C D : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hy : ay A D ≠ []) (hn : an A D ≠ []) :
    ∀ K, K ∈ classes A B C D → K ≠ [] := by
  intro K hK
  simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hK
  rcases hK with rfl | rfl | rfl | rfl
  · exact hy
  · exact hn
  · exact partitionCheck_nonempty _ _ hp K (by simp)
  · exact partitionCheck_nonempty _ _ hp K (by simp)

theorem classes_member_source (S : Tree) (A B C D K : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true) (hK : K ∈ classes A B C D) : Sub K (leaves S) := by
  intro x hx
  apply (parent_cover S A B C hp x).2
  simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hK
  rcases hK with rfl | rfl | rfl | rfl
  · exact Or.inl (List.mem_filter.1 hx).1
  · exact Or.inl (List.mem_filter.1 hx).1
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr hx)

/-- Each of the four actual full color classes has the printed labels. -/
theorem classes_color (S : Tree) (A B C D K : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true) (hK : K ∈ classes A B C D)
    (x : Nat) (hx : x ∈ K) (y : Nat) :
    y ∈ K ↔ y ∈ leaves S ∧ cheapColor A B D y = cheapColor A B D x := by
  have hxs := classes_member_source S A B C D K hp hK x hx
  have hcvx := class_values S A B C D hp x hxs
  by_cases hys : y ∈ leaves S
  · have hcvy := class_values S A B C D hp y hys
    simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hK
    rcases hK with rfl | rfl | rfl | rfl
    · rw [←hcvy.1,(hcvx.1).2 hx]; simp [hys]
    · rw [←hcvy.2.1,(hcvx.2.1).2 hx]; simp [hys]
    · rw [←hcvy.2.2.1,(hcvx.2.2.1).2 hx]; simp [hys]
    · rw [←hcvy.2.2.2,(hcvx.2.2.2).2 hx]; simp [hys]
  · constructor
    · intro hy; exact False.elim (hys (classes_member_source S A B C D K hp hK y hy))
    · intro hy; exact False.elim (hys hy.1)

/-- Every actual cheap block is one whole printed sector/parent; every printed
sector/parent occurs. Block order and internal label order are unrestricted. -/
theorem cheap_exact_classes (S : Tree) (A B C D : List Nat) (o : Output)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hy : ay A D ≠ []) (hn : an A D ≠ [])
    (hop : partitionCheck (leaves S) o.partition = true)
    (hc : ∀ K, K ∈ o.partition → ∀ y, y ∈ K ↔ y ∈ leaves S ∧ cheapColor A B D y = cheapColor A B D (K.headD 0)) :
    (∀ K, K ∈ o.partition → ∃ L, L ∈ classes A B C D ∧ SameMembers K L) ∧
    (∀ L, L ∈ classes A B C D → ∃ K, K ∈ o.partition ∧ SameMembers K L) := by
  have owner : ∀ x, x ∈ leaves S → ∃ L, L ∈ classes A B C D ∧ x ∈ L := by
    intro x hx
    rcases (parent_cover S A B C hp x).1 hx with ha | hb | hcc
    · by_cases hd : x ∈ D
      · exact ⟨ay A D,by simp [classes],by simp [ay,yes,ha,hd]⟩
      · exact ⟨an A D,by simp [classes],by simp [an,no,ha,hd]⟩
    · exact ⟨B,by simp [classes],hb⟩
    · exact ⟨C,by simp [classes],hcc⟩
  have same : ∀ K, K ∈ o.partition → ∀ L, L ∈ classes A B C D → ∀ x, x ∈ K → x ∈ L → SameMembers K L := by
    intro K hK L hL x hxK hxL y
    have hhead := (hc K hK x).1 hxK
    rw [hc K hK y,classes_color S A B C D L hp hL x hxL y,hhead.2]
  constructor
  · intro K hK
    obtain ⟨x,hx⟩ := nonempty_witness K (partitionCheck_nonempty _ _ hop K hK)
    obtain ⟨L,hL,hxL⟩ := owner x ((hc K hK x).1 hx).1
    exact ⟨L,hL,same K hK L hL x hx hxL⟩
  · intro L hL
    obtain ⟨x,hx⟩ := nonempty_witness L (classes_nonempty S A B C D hp hy hn L hL)
    obtain ⟨K,hK,hxK⟩ := Integration.partitionCheck_covers _ _ hop x (classes_member_source S A B C D L hp hL x hx)
    exact ⟨K,hK,same K hK L hL x hxK hx⟩

theorem classes_target (T : Tree) (A B C D : List Nat)
    (hs : Disj T (ay A D) (an A D))
    (hy : Disj T (ay A D) B) (hn : Disj T (an A D) B)
    (hac : Disj T A C) (hbc : Disj T B C) :
    (classes A B C D).Pairwise (Disj T) := by
  simp only [classes,List.pairwise_cons]
  refine ⟨?_,⟨?_,⟨?_,by simp⟩⟩⟩
  · intro L hL
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
    rcases hL with rfl | rfl | rfl
    · exact hs
    · exact hy
    · exact disj_mono hac (fun x hx => (List.mem_filter.1 hx).1) (fun _ h => h)
  · intro L hL
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
    rcases hL with rfl | rfl
    · exact hn
    · exact disj_mono hac (fun x hx => (List.mem_filter.1 hx).1) (fun _ h => h)
  · intro L hL
    have he : L = C := by simpa using hL
    subst L
    exact hbc
end Universal233.BinaryCheap
