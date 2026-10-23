import HardForest
import Interface

namespace Universal233.PairAssembly
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange

def sideColor (D : List Nat) (x : Nat) : Nat := if x ∈ D then 0 else 1

def sideOutputs (S : Tree) (A B D : List Nat) (q : Nat) : List Output :=
  WholeSourceMass.wholeOutputs S A B (fun _ => 0) (sideColor D) (fun _ => 0) q

theorem side_mono_of_sector (D L : List Nat)
    (h : (∀ x, x ∈ L → x ∈ D) ∨ (∀ x, x ∈ L → x ∉ D)) :
    LabelMonochromatic (sideColor D) L := by
  intro x y hx hy
  rcases h with h | h <;> simp [sideColor,h x hx,h y hy]

theorem side_mono_sectors (D L : List Nat) (hne : L ≠ [])
    (hm : LabelMonochromatic (sideColor D) L) :
    (∀ x, x ∈ L → x ∈ D) ∨ (∀ x, x ∈ L → x ∉ D) := by
  obtain ⟨x,hx⟩ := nonempty_witness L hne
  by_cases hxd : x ∈ D
  · left
    intro y hy
    have h := hm x y hx hy
    by_cases hyd : y ∈ D
    · exact hyd
    · simp [sideColor,hxd,hyd] at h
  · right
    intro y hy hyd
    have h := hm x y hx hy
    simp [sideColor,hxd,hyd] at h

theorem side_color_count (B D : List Nat)
    (hy : yes B ((D.contains ·)) ≠ []) (hn : no B ((D.contains ·)) ≠ []) :
    (WholeSourceMass.localColors B (sideColor D)).length = 2 := by
  apply WholeSourceMass.same_members_length _ [0,1] (WholeSourceMass.localColors_nodup _ _) (by decide)
  intro i
  rw [WholeSourceMass.mem_localColors]
  constructor
  · rintro ⟨x,hx,rfl⟩
    by_cases hd : x ∈ D <;> simp [sideColor,hd]
  · intro hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · obtain ⟨x,hx⟩ := nonempty_witness _ hy
      have hx' : x ∈ B ∧ x ∈ D := by simpa [yes] using hx
      exact ⟨x,hx'.1,by simp [sideColor,hx'.2]⟩
    · obtain ⟨x,hx⟩ := nonempty_witness _ hn
      have hx' : x ∈ B ∧ x ∉ D := by simpa [no] using hx
      exact ⟨x,hx'.1,by simp [sideColor,hx'.2]⟩

theorem side_input_color_count (S T : Tree) (A B C D : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (ht : (leaves T).Nodup) (hl : ∀ x, x ∈ leaves S → x ∈ leaves T)
    (hy : yes B ((D.contains ·)) ≠ []) (hn : no B ((D.contains ·)) ≠ []) :
    (dedupNat ((leaves S).map (WholeSourceMass.taggedColor A B (fun _ => 0) (sideColor D) (fun _ => 0)))).length = 4 := by
  have hc := PaidAssembly.partition_mass_interface S T A B C hp ht hl
  rw [WholeSourceMass.taggedColor_cardinality S A B C hc.partition,
    WholeSourceMass.localColors_zero A hc.aNonempty,side_color_count B D hy hn,
    WholeSourceMass.localColors_zero C hc.cNonempty]

theorem side_raw_mass (S T : Tree) (A B C D : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (ht : (leaves T).Nodup) (hl : ∀ x, x ∈ leaves S → x ∈ leaves T)
    (hy : yes B ((D.contains ·)) ≠ []) (hn : no B ((D.contains ·)) ≠ [])
    (q : Nat) (c : Rat) (hc : 2 ≤ c) : rawQMass c (sideOutputs S A B D q) ≤ c^(-3 : Int) := by
  apply WholeSourceMass.generate_mass_of_count S _ q 3 c hc
  rw [side_input_color_count S T A B C D hp ht hl hy hn]
  decide

/-- Every ACTUAL generated B block is inside one mutual-clear sector. -/
theorem side_output_clear (S T : Tree) (A B C D : List Nat) (q : Nat) (o : Output)
    (ho : o ∈ sideOutputs S A B D q)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hyes : Disj T (yes B ((D.contains ·))) A)
    (hno : Disj T (no B ((D.contains ·))) A) :
    ∀ K, K ∈ o.partition → Sub K B → Disj T K A := by
  obtain ⟨hab,_,_⟩ := Assembly.parent_partition_disjoint S A B C hp
  have hmono := CutRealization.generate_monochromatic S _ q o ho
  have hpart := CutRealization.generate_partition_check S _ q o ho
  intro K hK hKB
  have hm := Assembly.tagged_extract_B A B K (fun _ => 0) (sideColor D) (fun _ => 0) hab hKB (hmono K hK)
  have hne := partitionCheck_nonempty _ _ hpart K hK
  rcases side_mono_sectors D K hne hm with hy | hn
  · exact disj_mono hyes (by intro x hx; simp [yes,hKB x hx,hy x hx]) (by intro x hx; exact hx)
  · exact disj_mono hno (by intro x hx; simp [no,hKB x hx,hn x hx]) (by intro x hx; exact hx)
end Universal233.PairAssembly
