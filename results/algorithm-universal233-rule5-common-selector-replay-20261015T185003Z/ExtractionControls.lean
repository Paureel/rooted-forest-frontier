import CurrentPartition
namespace Universal233.Case322Extraction.Controls
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322 Universal233.Case322Extraction
set_option maxRecDepth 24000
def i0nT : Tree := (.node (.leaf 4) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node (.leaf 3) (.leaf 2))))))))))))
def i0nS : Tree := (.node ((.node ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))) (.leaf 2))) (.leaf 1))
theorem i0n_guards : (rawPlan i0nT i0nS 0 1 2 [true,false,false] [true] [true,false,true] [true,true,true,true,true,true]).all (currentGuard i0nT i0nS) = true := by decide
theorem i0n_costs : (rawPlan i0nT i0nS 0 1 2 [true,false,false] [true] [true,false,true] [true,true,true,true,true,true]).map paid = [2,1,2,2] := by decide
theorem i0n_cover (F : List (List Nat)) (ha : agreement i0nT i0nS F = true) : ∃ child, child ∈ rawPlan i0nT i0nS 0 1 2 [true,false,false] [true] [true,false,true] [true,true,true,true,true,true] ∧ OriginalCover i0nT i0nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,false]) (sa := false) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [i0nT,i0nS,leaves]; omega)
def i0mT : Tree := (.node ((.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) (.leaf 7))) (.leaf 5))) (.leaf 6))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 4))
def i0mS : Tree := (.node ((.node ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))) (.leaf 2))) (.leaf 1))
theorem i0m_guards : (rawPlan i0mT i0mS 0 1 2 [false,true,true] [true] [false,true,false] [false,false,false,false,false,false]).all (currentGuard i0mT i0mS) = true := by decide
theorem i0m_costs : (rawPlan i0mT i0mS 0 1 2 [false,true,true] [true] [false,true,false] [false,false,false,false,false,false]).map paid = [2,1,2,2] := by decide
theorem i0m_cover (F : List (List Nat)) (ha : agreement i0mT i0mS F = true) : ∃ child, child ∈ rawPlan i0mT i0mS 0 1 2 [false,true,true] [true] [false,true,false] [false,false,false,false,false,false] ∧ OriginalCover i0mT i0mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,true]) (sa := false) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [i0mT,i0mS,leaves]; omega)
def i1nT : Tree := (.node (.leaf 4) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node (.leaf 3) (.leaf 2))))))))))))
def i1nS : Tree := (.node ((.node ((.node ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 0))) (.leaf 2))) (.leaf 1))
theorem i1n_guards : (rawPlan i1nT i1nS 0 1 2 [true,false,false] [true] [true,false,true] [true,true,true,true,true,true]).all (currentGuard i1nT i1nS) = true := by decide
theorem i1n_costs : (rawPlan i1nT i1nS 0 1 2 [true,false,false] [true] [true,false,true] [true,true,true,true,true,true]).map paid = [2,1,2,2] := by decide
theorem i1n_cover (F : List (List Nat)) (ha : agreement i1nT i1nS F = true) : ∃ child, child ∈ rawPlan i1nT i1nS 0 1 2 [true,false,false] [true] [true,false,true] [true,true,true,true,true,true] ∧ OriginalCover i1nT i1nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,false]) (sa := true) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [i1nT,i1nS,leaves]; omega)
def i1mT : Tree := (.node ((.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) (.leaf 7))) (.leaf 5))) (.leaf 6))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 4))
def i1mS : Tree := (.node ((.node ((.node ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 0))) (.leaf 2))) (.leaf 1))
theorem i1m_guards : (rawPlan i1mT i1mS 0 1 2 [false,true,true] [true] [false,true,false] [false,false,false,false,false,false]).all (currentGuard i1mT i1mS) = true := by decide
theorem i1m_costs : (rawPlan i1mT i1mS 0 1 2 [false,true,true] [true] [false,true,false] [false,false,false,false,false,false]).map paid = [2,1,2,2] := by decide
theorem i1m_cover (F : List (List Nat)) (ha : agreement i1mT i1mS F = true) : ∃ child, child ∈ rawPlan i1mT i1mS 0 1 2 [false,true,true] [true] [false,true,false] [false,false,false,false,false,false] ∧ OriginalCover i1mT i1mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,true]) (sa := true) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [i1mT,i1mS,leaves]; omega)
def i2nT : Tree := (.node (.leaf 4) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node (.leaf 3) (.leaf 2))))))))))))
def i2nS : Tree := (.node ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))))) (.leaf 1))
theorem i2n_guards : (rawPlan i2nT i2nS 0 1 2 [true,false,false] [true] [true,false,true] [true,true,true,true,true,true]).all (currentGuard i2nT i2nS) = true := by decide
theorem i2n_costs : (rawPlan i2nT i2nS 0 1 2 [true,false,false] [true] [true,false,true] [true,true,true,true,true,true]).map paid = [2,1,2,2] := by decide
theorem i2n_cover (F : List (List Nat)) (ha : agreement i2nT i2nS F = true) : ∃ child, child ∈ rawPlan i2nT i2nS 0 1 2 [true,false,false] [true] [true,false,true] [true,true,true,true,true,true] ∧ OriginalCover i2nT i2nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,false]) (sa := false) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [i2nT,i2nS,leaves]; omega)
def i2mT : Tree := (.node ((.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) (.leaf 7))) (.leaf 5))) (.leaf 6))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 4))
def i2mS : Tree := (.node ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))))) (.leaf 1))
theorem i2m_guards : (rawPlan i2mT i2mS 0 1 2 [false,true,true] [true] [false,true,false] [false,false,false,false,false,false]).all (currentGuard i2mT i2mS) = true := by decide
theorem i2m_costs : (rawPlan i2mT i2mS 0 1 2 [false,true,true] [true] [false,true,false] [false,false,false,false,false,false]).map paid = [2,1,2,2] := by decide
theorem i2m_cover (F : List (List Nat)) (ha : agreement i2mT i2mS F = true) : ∃ child, child ∈ rawPlan i2mT i2mS 0 1 2 [false,true,true] [true] [false,true,false] [false,false,false,false,false,false] ∧ OriginalCover i2mT i2mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,true]) (sa := false) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [i2mT,i2mS,leaves]; omega)
def i3nT : Tree := (.node (.leaf 4) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node (.leaf 3) (.leaf 2))))))))))))
def i3nS : Tree := (.node ((.node (.leaf 2) ((.node ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 0))))) (.leaf 1))
theorem i3n_guards : (rawPlan i3nT i3nS 0 1 2 [true,false,false] [true] [true,false,true] [true,true,true,true,true,true]).all (currentGuard i3nT i3nS) = true := by decide
theorem i3n_costs : (rawPlan i3nT i3nS 0 1 2 [true,false,false] [true] [true,false,true] [true,true,true,true,true,true]).map paid = [2,1,2,2] := by decide
theorem i3n_cover (F : List (List Nat)) (ha : agreement i3nT i3nS F = true) : ∃ child, child ∈ rawPlan i3nT i3nS 0 1 2 [true,false,false] [true] [true,false,true] [true,true,true,true,true,true] ∧ OriginalCover i3nT i3nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,false]) (sa := true) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [i3nT,i3nS,leaves]; omega)
def i3mT : Tree := (.node ((.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) (.leaf 7))) (.leaf 5))) (.leaf 6))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 4))
def i3mS : Tree := (.node ((.node (.leaf 2) ((.node ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 0))))) (.leaf 1))
theorem i3m_guards : (rawPlan i3mT i3mS 0 1 2 [false,true,true] [true] [false,true,false] [false,false,false,false,false,false]).all (currentGuard i3mT i3mS) = true := by decide
theorem i3m_costs : (rawPlan i3mT i3mS 0 1 2 [false,true,true] [true] [false,true,false] [false,false,false,false,false,false]).map paid = [2,1,2,2] := by decide
theorem i3m_cover (F : List (List Nat)) (ha : agreement i3mT i3mS F = true) : ∃ child, child ∈ rawPlan i3mT i3mS 0 1 2 [false,true,true] [true] [false,true,false] [false,false,false,false,false,false] ∧ OriginalCover i3mT i3mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,true]) (sa := true) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [i3mT,i3mS,leaves]; omega)
def i4nT : Tree := (.node (.leaf 4) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node (.leaf 3) (.leaf 2))))))))))))
def i4nS : Tree := (.node (.leaf 1) ((.node ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))) (.leaf 2))))
theorem i4n_guards : (rawPlan i4nT i4nS 0 1 2 [true,false,false] [false] [true,false,true] [true,true,true,true,true,true]).all (currentGuard i4nT i4nS) = true := by decide
theorem i4n_costs : (rawPlan i4nT i4nS 0 1 2 [true,false,false] [false] [true,false,true] [true,true,true,true,true,true]).map paid = [2,1,2,2] := by decide
theorem i4n_cover (F : List (List Nat)) (ha : agreement i4nT i4nS F = true) : ∃ child, child ∈ rawPlan i4nT i4nS 0 1 2 [true,false,false] [false] [true,false,true] [true,true,true,true,true,true] ∧ OriginalCover i4nT i4nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,false]) (sa := false) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [i4nT,i4nS,leaves]; omega)
def i4mT : Tree := (.node ((.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) (.leaf 7))) (.leaf 5))) (.leaf 6))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 4))
def i4mS : Tree := (.node (.leaf 1) ((.node ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))) (.leaf 2))))
theorem i4m_guards : (rawPlan i4mT i4mS 0 1 2 [false,true,true] [false] [false,true,false] [false,false,false,false,false,false]).all (currentGuard i4mT i4mS) = true := by decide
theorem i4m_costs : (rawPlan i4mT i4mS 0 1 2 [false,true,true] [false] [false,true,false] [false,false,false,false,false,false]).map paid = [2,1,2,2] := by decide
theorem i4m_cover (F : List (List Nat)) (ha : agreement i4mT i4mS F = true) : ∃ child, child ∈ rawPlan i4mT i4mS 0 1 2 [false,true,true] [false] [false,true,false] [false,false,false,false,false,false] ∧ OriginalCover i4mT i4mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,true]) (sa := false) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [i4mT,i4mS,leaves]; omega)
def i5nT : Tree := (.node (.leaf 4) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node (.leaf 3) (.leaf 2))))))))))))
def i5nS : Tree := (.node (.leaf 1) ((.node ((.node ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 0))) (.leaf 2))))
theorem i5n_guards : (rawPlan i5nT i5nS 0 1 2 [true,false,false] [false] [true,false,true] [true,true,true,true,true,true]).all (currentGuard i5nT i5nS) = true := by decide
theorem i5n_costs : (rawPlan i5nT i5nS 0 1 2 [true,false,false] [false] [true,false,true] [true,true,true,true,true,true]).map paid = [2,1,2,2] := by decide
theorem i5n_cover (F : List (List Nat)) (ha : agreement i5nT i5nS F = true) : ∃ child, child ∈ rawPlan i5nT i5nS 0 1 2 [true,false,false] [false] [true,false,true] [true,true,true,true,true,true] ∧ OriginalCover i5nT i5nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,false]) (sa := true) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [i5nT,i5nS,leaves]; omega)
def i5mT : Tree := (.node ((.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) (.leaf 7))) (.leaf 5))) (.leaf 6))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 4))
def i5mS : Tree := (.node (.leaf 1) ((.node ((.node ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 0))) (.leaf 2))))
theorem i5m_guards : (rawPlan i5mT i5mS 0 1 2 [false,true,true] [false] [false,true,false] [false,false,false,false,false,false]).all (currentGuard i5mT i5mS) = true := by decide
theorem i5m_costs : (rawPlan i5mT i5mS 0 1 2 [false,true,true] [false] [false,true,false] [false,false,false,false,false,false]).map paid = [2,1,2,2] := by decide
theorem i5m_cover (F : List (List Nat)) (ha : agreement i5mT i5mS F = true) : ∃ child, child ∈ rawPlan i5mT i5mS 0 1 2 [false,true,true] [false] [false,true,false] [false,false,false,false,false,false] ∧ OriginalCover i5mT i5mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,true]) (sa := true) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [i5mT,i5mS,leaves]; omega)
def i6nT : Tree := (.node (.leaf 4) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node (.leaf 3) (.leaf 2))))))))))))
def i6nS : Tree := (.node (.leaf 1) ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))))))
theorem i6n_guards : (rawPlan i6nT i6nS 0 1 2 [true,false,false] [false] [true,false,true] [true,true,true,true,true,true]).all (currentGuard i6nT i6nS) = true := by decide
theorem i6n_costs : (rawPlan i6nT i6nS 0 1 2 [true,false,false] [false] [true,false,true] [true,true,true,true,true,true]).map paid = [2,1,2,2] := by decide
theorem i6n_cover (F : List (List Nat)) (ha : agreement i6nT i6nS F = true) : ∃ child, child ∈ rawPlan i6nT i6nS 0 1 2 [true,false,false] [false] [true,false,true] [true,true,true,true,true,true] ∧ OriginalCover i6nT i6nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,false]) (sa := false) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [i6nT,i6nS,leaves]; omega)
def i6mT : Tree := (.node ((.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) (.leaf 7))) (.leaf 5))) (.leaf 6))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 4))
def i6mS : Tree := (.node (.leaf 1) ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))))))
theorem i6m_guards : (rawPlan i6mT i6mS 0 1 2 [false,true,true] [false] [false,true,false] [false,false,false,false,false,false]).all (currentGuard i6mT i6mS) = true := by decide
theorem i6m_costs : (rawPlan i6mT i6mS 0 1 2 [false,true,true] [false] [false,true,false] [false,false,false,false,false,false]).map paid = [2,1,2,2] := by decide
theorem i6m_cover (F : List (List Nat)) (ha : agreement i6mT i6mS F = true) : ∃ child, child ∈ rawPlan i6mT i6mS 0 1 2 [false,true,true] [false] [false,true,false] [false,false,false,false,false,false] ∧ OriginalCover i6mT i6mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,true]) (sa := false) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [i6mT,i6mS,leaves]; omega)
def i7nT : Tree := (.node (.leaf 4) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node (.leaf 3) (.leaf 2))))))))))))
def i7nS : Tree := (.node (.leaf 1) ((.node (.leaf 2) ((.node ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 0))))))
theorem i7n_guards : (rawPlan i7nT i7nS 0 1 2 [true,false,false] [false] [true,false,true] [true,true,true,true,true,true]).all (currentGuard i7nT i7nS) = true := by decide
theorem i7n_costs : (rawPlan i7nT i7nS 0 1 2 [true,false,false] [false] [true,false,true] [true,true,true,true,true,true]).map paid = [2,1,2,2] := by decide
theorem i7n_cover (F : List (List Nat)) (ha : agreement i7nT i7nS F = true) : ∃ child, child ∈ rawPlan i7nT i7nS 0 1 2 [true,false,false] [false] [true,false,true] [true,true,true,true,true,true] ∧ OriginalCover i7nT i7nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,false]) (sa := true) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [i7nT,i7nS,leaves]; omega)
def i7mT : Tree := (.node ((.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) (.leaf 7))) (.leaf 5))) (.leaf 6))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 4))
def i7mS : Tree := (.node (.leaf 1) ((.node (.leaf 2) ((.node ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 0))))))
theorem i7m_guards : (rawPlan i7mT i7mS 0 1 2 [false,true,true] [false] [false,true,false] [false,false,false,false,false,false]).all (currentGuard i7mT i7mS) = true := by decide
theorem i7m_costs : (rawPlan i7mT i7mS 0 1 2 [false,true,true] [false] [false,true,false] [false,false,false,false,false,false]).map paid = [2,1,2,2] := by decide
theorem i7m_cover (F : List (List Nat)) (ha : agreement i7mT i7mS F = true) : ∃ child, child ∈ rawPlan i7mT i7mS 0 1 2 [false,true,true] [false] [false,true,false] [false,false,false,false,false,false] ∧ OriginalCover i7mT i7mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,true]) (sa := true) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [i7mT,i7mS,leaves]; omega)
def ii0nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 0) (.leaf 1))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def ii0nS : Tree := (.node ((.node ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))) (.leaf 2))) (.leaf 1))
theorem ii0n_guards : (rawPlan ii0nT ii0nS 0 1 2 [false,false,false,true,false] [true] [false,false,false,true,true] [false,true]).all (currentGuard ii0nT ii0nS) = true := by decide
theorem ii0n_costs : (rawPlan ii0nT ii0nS 0 1 2 [false,false,false,true,false] [true] [false,false,false,true,true] [false,true]).map paid = [2,1,3] := by decide
theorem ii0n_cover (F : List (List Nat)) (ha : agreement ii0nT ii0nS F = true) : ∃ child, child ∈ rawPlan ii0nT ii0nS 0 1 2 [false,false,false,true,false] [true] [false,false,false,true,true] [false,true] ∧ OriginalCover ii0nT ii0nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [false,false,false,true]) (sa := false) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inl rfl⟩ | rfl | decide | (intro x; simp [ii0nT,ii0nS,leaves]; omega)
def ii0mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 1) (.leaf 0))) (.leaf 5))))))))
def ii0mS : Tree := (.node ((.node ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))) (.leaf 2))) (.leaf 1))
theorem ii0m_guards : (rawPlan ii0mT ii0mS 0 1 2 [true,true,true,false,true] [true] [true,true,true,false,false] [true,false]).all (currentGuard ii0mT ii0mS) = true := by decide
theorem ii0m_costs : (rawPlan ii0mT ii0mS 0 1 2 [true,true,true,false,true] [true] [true,true,true,false,false] [true,false]).map paid = [2,1,3] := by decide
theorem ii0m_cover (F : List (List Nat)) (ha : agreement ii0mT ii0mS F = true) : ∃ child, child ∈ rawPlan ii0mT ii0mS 0 1 2 [true,true,true,false,true] [true] [true,true,true,false,false] [true,false] ∧ OriginalCover ii0mT ii0mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [true,true,true,false]) (sa := false) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inr rfl⟩ | rfl | decide | (intro x; simp [ii0mT,ii0mS,leaves]; omega)
def ii1nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 0) (.leaf 1))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def ii1nS : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))) (.leaf 2))) (.leaf 1))
theorem ii1n_guards : (rawPlan ii1nT ii1nS 0 1 2 [false,false,false,true,false] [true] [false,false,false,true,true] [false,true]).all (currentGuard ii1nT ii1nS) = true := by decide
theorem ii1n_costs : (rawPlan ii1nT ii1nS 0 1 2 [false,false,false,true,false] [true] [false,false,false,true,true] [false,true]).map paid = [2,1,3] := by decide
theorem ii1n_cover (F : List (List Nat)) (ha : agreement ii1nT ii1nS F = true) : ∃ child, child ∈ rawPlan ii1nT ii1nS 0 1 2 [false,false,false,true,false] [true] [false,false,false,true,true] [false,true] ∧ OriginalCover ii1nT ii1nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [false,false,false,true]) (sa := true) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inl rfl⟩ | rfl | decide | (intro x; simp [ii1nT,ii1nS,leaves]; omega)
def ii1mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 1) (.leaf 0))) (.leaf 5))))))))
def ii1mS : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))) (.leaf 2))) (.leaf 1))
theorem ii1m_guards : (rawPlan ii1mT ii1mS 0 1 2 [true,true,true,false,true] [true] [true,true,true,false,false] [true,false]).all (currentGuard ii1mT ii1mS) = true := by decide
theorem ii1m_costs : (rawPlan ii1mT ii1mS 0 1 2 [true,true,true,false,true] [true] [true,true,true,false,false] [true,false]).map paid = [2,1,3] := by decide
theorem ii1m_cover (F : List (List Nat)) (ha : agreement ii1mT ii1mS F = true) : ∃ child, child ∈ rawPlan ii1mT ii1mS 0 1 2 [true,true,true,false,true] [true] [true,true,true,false,false] [true,false] ∧ OriginalCover ii1mT ii1mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [true,true,true,false]) (sa := true) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inr rfl⟩ | rfl | decide | (intro x; simp [ii1mT,ii1mS,leaves]; omega)
def ii2nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 0) (.leaf 1))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def ii2nS : Tree := (.node ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))))) (.leaf 1))
theorem ii2n_guards : (rawPlan ii2nT ii2nS 0 1 2 [false,false,false,true,false] [true] [false,false,false,true,true] [false,true]).all (currentGuard ii2nT ii2nS) = true := by decide
theorem ii2n_costs : (rawPlan ii2nT ii2nS 0 1 2 [false,false,false,true,false] [true] [false,false,false,true,true] [false,true]).map paid = [2,1,3] := by decide
theorem ii2n_cover (F : List (List Nat)) (ha : agreement ii2nT ii2nS F = true) : ∃ child, child ∈ rawPlan ii2nT ii2nS 0 1 2 [false,false,false,true,false] [true] [false,false,false,true,true] [false,true] ∧ OriginalCover ii2nT ii2nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [false,false,false,true]) (sa := false) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inl rfl⟩ | rfl | decide | (intro x; simp [ii2nT,ii2nS,leaves]; omega)
def ii2mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 1) (.leaf 0))) (.leaf 5))))))))
def ii2mS : Tree := (.node ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))))) (.leaf 1))
theorem ii2m_guards : (rawPlan ii2mT ii2mS 0 1 2 [true,true,true,false,true] [true] [true,true,true,false,false] [true,false]).all (currentGuard ii2mT ii2mS) = true := by decide
theorem ii2m_costs : (rawPlan ii2mT ii2mS 0 1 2 [true,true,true,false,true] [true] [true,true,true,false,false] [true,false]).map paid = [2,1,3] := by decide
theorem ii2m_cover (F : List (List Nat)) (ha : agreement ii2mT ii2mS F = true) : ∃ child, child ∈ rawPlan ii2mT ii2mS 0 1 2 [true,true,true,false,true] [true] [true,true,true,false,false] [true,false] ∧ OriginalCover ii2mT ii2mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [true,true,true,false]) (sa := false) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inr rfl⟩ | rfl | decide | (intro x; simp [ii2mT,ii2mS,leaves]; omega)
def ii3nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 0) (.leaf 1))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def ii3nS : Tree := (.node ((.node (.leaf 2) ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))))) (.leaf 1))
theorem ii3n_guards : (rawPlan ii3nT ii3nS 0 1 2 [false,false,false,true,false] [true] [false,false,false,true,true] [false,true]).all (currentGuard ii3nT ii3nS) = true := by decide
theorem ii3n_costs : (rawPlan ii3nT ii3nS 0 1 2 [false,false,false,true,false] [true] [false,false,false,true,true] [false,true]).map paid = [2,1,3] := by decide
theorem ii3n_cover (F : List (List Nat)) (ha : agreement ii3nT ii3nS F = true) : ∃ child, child ∈ rawPlan ii3nT ii3nS 0 1 2 [false,false,false,true,false] [true] [false,false,false,true,true] [false,true] ∧ OriginalCover ii3nT ii3nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [false,false,false,true]) (sa := true) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inl rfl⟩ | rfl | decide | (intro x; simp [ii3nT,ii3nS,leaves]; omega)
def ii3mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 1) (.leaf 0))) (.leaf 5))))))))
def ii3mS : Tree := (.node ((.node (.leaf 2) ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))))) (.leaf 1))
theorem ii3m_guards : (rawPlan ii3mT ii3mS 0 1 2 [true,true,true,false,true] [true] [true,true,true,false,false] [true,false]).all (currentGuard ii3mT ii3mS) = true := by decide
theorem ii3m_costs : (rawPlan ii3mT ii3mS 0 1 2 [true,true,true,false,true] [true] [true,true,true,false,false] [true,false]).map paid = [2,1,3] := by decide
theorem ii3m_cover (F : List (List Nat)) (ha : agreement ii3mT ii3mS F = true) : ∃ child, child ∈ rawPlan ii3mT ii3mS 0 1 2 [true,true,true,false,true] [true] [true,true,true,false,false] [true,false] ∧ OriginalCover ii3mT ii3mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [true,true,true,false]) (sa := true) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inr rfl⟩ | rfl | decide | (intro x; simp [ii3mT,ii3mS,leaves]; omega)
def ii4nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 0) (.leaf 1))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def ii4nS : Tree := (.node (.leaf 1) ((.node ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))) (.leaf 2))))
theorem ii4n_guards : (rawPlan ii4nT ii4nS 0 1 2 [false,false,false,true,false] [false] [false,false,false,true,true] [false,true]).all (currentGuard ii4nT ii4nS) = true := by decide
theorem ii4n_costs : (rawPlan ii4nT ii4nS 0 1 2 [false,false,false,true,false] [false] [false,false,false,true,true] [false,true]).map paid = [2,1,3] := by decide
theorem ii4n_cover (F : List (List Nat)) (ha : agreement ii4nT ii4nS F = true) : ∃ child, child ∈ rawPlan ii4nT ii4nS 0 1 2 [false,false,false,true,false] [false] [false,false,false,true,true] [false,true] ∧ OriginalCover ii4nT ii4nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [false,false,false,true]) (sa := false) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inl rfl⟩ | rfl | decide | (intro x; simp [ii4nT,ii4nS,leaves]; omega)
def ii4mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 1) (.leaf 0))) (.leaf 5))))))))
def ii4mS : Tree := (.node (.leaf 1) ((.node ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))) (.leaf 2))))
theorem ii4m_guards : (rawPlan ii4mT ii4mS 0 1 2 [true,true,true,false,true] [false] [true,true,true,false,false] [true,false]).all (currentGuard ii4mT ii4mS) = true := by decide
theorem ii4m_costs : (rawPlan ii4mT ii4mS 0 1 2 [true,true,true,false,true] [false] [true,true,true,false,false] [true,false]).map paid = [2,1,3] := by decide
theorem ii4m_cover (F : List (List Nat)) (ha : agreement ii4mT ii4mS F = true) : ∃ child, child ∈ rawPlan ii4mT ii4mS 0 1 2 [true,true,true,false,true] [false] [true,true,true,false,false] [true,false] ∧ OriginalCover ii4mT ii4mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [true,true,true,false]) (sa := false) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inr rfl⟩ | rfl | decide | (intro x; simp [ii4mT,ii4mS,leaves]; omega)
def ii5nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 0) (.leaf 1))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def ii5nS : Tree := (.node (.leaf 1) ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))) (.leaf 2))))
theorem ii5n_guards : (rawPlan ii5nT ii5nS 0 1 2 [false,false,false,true,false] [false] [false,false,false,true,true] [false,true]).all (currentGuard ii5nT ii5nS) = true := by decide
theorem ii5n_costs : (rawPlan ii5nT ii5nS 0 1 2 [false,false,false,true,false] [false] [false,false,false,true,true] [false,true]).map paid = [2,1,3] := by decide
theorem ii5n_cover (F : List (List Nat)) (ha : agreement ii5nT ii5nS F = true) : ∃ child, child ∈ rawPlan ii5nT ii5nS 0 1 2 [false,false,false,true,false] [false] [false,false,false,true,true] [false,true] ∧ OriginalCover ii5nT ii5nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [false,false,false,true]) (sa := true) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inl rfl⟩ | rfl | decide | (intro x; simp [ii5nT,ii5nS,leaves]; omega)
def ii5mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 1) (.leaf 0))) (.leaf 5))))))))
def ii5mS : Tree := (.node (.leaf 1) ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))) (.leaf 2))))
theorem ii5m_guards : (rawPlan ii5mT ii5mS 0 1 2 [true,true,true,false,true] [false] [true,true,true,false,false] [true,false]).all (currentGuard ii5mT ii5mS) = true := by decide
theorem ii5m_costs : (rawPlan ii5mT ii5mS 0 1 2 [true,true,true,false,true] [false] [true,true,true,false,false] [true,false]).map paid = [2,1,3] := by decide
theorem ii5m_cover (F : List (List Nat)) (ha : agreement ii5mT ii5mS F = true) : ∃ child, child ∈ rawPlan ii5mT ii5mS 0 1 2 [true,true,true,false,true] [false] [true,true,true,false,false] [true,false] ∧ OriginalCover ii5mT ii5mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [true,true,true,false]) (sa := true) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inr rfl⟩ | rfl | decide | (intro x; simp [ii5mT,ii5mS,leaves]; omega)
def ii6nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 0) (.leaf 1))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def ii6nS : Tree := (.node (.leaf 1) ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))))))
theorem ii6n_guards : (rawPlan ii6nT ii6nS 0 1 2 [false,false,false,true,false] [false] [false,false,false,true,true] [false,true]).all (currentGuard ii6nT ii6nS) = true := by decide
theorem ii6n_costs : (rawPlan ii6nT ii6nS 0 1 2 [false,false,false,true,false] [false] [false,false,false,true,true] [false,true]).map paid = [2,1,3] := by decide
theorem ii6n_cover (F : List (List Nat)) (ha : agreement ii6nT ii6nS F = true) : ∃ child, child ∈ rawPlan ii6nT ii6nS 0 1 2 [false,false,false,true,false] [false] [false,false,false,true,true] [false,true] ∧ OriginalCover ii6nT ii6nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [false,false,false,true]) (sa := false) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inl rfl⟩ | rfl | decide | (intro x; simp [ii6nT,ii6nS,leaves]; omega)
def ii6mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 1) (.leaf 0))) (.leaf 5))))))))
def ii6mS : Tree := (.node (.leaf 1) ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))))))
theorem ii6m_guards : (rawPlan ii6mT ii6mS 0 1 2 [true,true,true,false,true] [false] [true,true,true,false,false] [true,false]).all (currentGuard ii6mT ii6mS) = true := by decide
theorem ii6m_costs : (rawPlan ii6mT ii6mS 0 1 2 [true,true,true,false,true] [false] [true,true,true,false,false] [true,false]).map paid = [2,1,3] := by decide
theorem ii6m_cover (F : List (List Nat)) (ha : agreement ii6mT ii6mS F = true) : ∃ child, child ∈ rawPlan ii6mT ii6mS 0 1 2 [true,true,true,false,true] [false] [true,true,true,false,false] [true,false] ∧ OriginalCover ii6mT ii6mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [true,true,true,false]) (sa := false) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inr rfl⟩ | rfl | decide | (intro x; simp [ii6mT,ii6mS,leaves]; omega)
def ii7nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 0) (.leaf 1))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def ii7nS : Tree := (.node (.leaf 1) ((.node (.leaf 2) ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))))))
theorem ii7n_guards : (rawPlan ii7nT ii7nS 0 1 2 [false,false,false,true,false] [false] [false,false,false,true,true] [false,true]).all (currentGuard ii7nT ii7nS) = true := by decide
theorem ii7n_costs : (rawPlan ii7nT ii7nS 0 1 2 [false,false,false,true,false] [false] [false,false,false,true,true] [false,true]).map paid = [2,1,3] := by decide
theorem ii7n_cover (F : List (List Nat)) (ha : agreement ii7nT ii7nS F = true) : ∃ child, child ∈ rawPlan ii7nT ii7nS 0 1 2 [false,false,false,true,false] [false] [false,false,false,true,true] [false,true] ∧ OriginalCover ii7nT ii7nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [false,false,false,true]) (sa := true) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inl rfl⟩ | rfl | decide | (intro x; simp [ii7nT,ii7nS,leaves]; omega)
def ii7mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 1) (.leaf 0))) (.leaf 5))))))))
def ii7mS : Tree := (.node (.leaf 1) ((.node (.leaf 2) ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))))))
theorem ii7m_guards : (rawPlan ii7mT ii7mS 0 1 2 [true,true,true,false,true] [false] [true,true,true,false,false] [true,false]).all (currentGuard ii7mT ii7mS) = true := by decide
theorem ii7m_costs : (rawPlan ii7mT ii7mS 0 1 2 [true,true,true,false,true] [false] [true,true,true,false,false] [true,false]).map paid = [2,1,3] := by decide
theorem ii7m_cover (F : List (List Nat)) (ha : agreement ii7mT ii7mS F = true) : ∃ child, child ∈ rawPlan ii7mT ii7mS 0 1 2 [true,true,true,false,true] [false] [true,true,true,false,false] [true,false] ∧ OriginalCover ii7mT ii7mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [true,true,true,false]) (sa := true) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inr rfl⟩ | rfl | decide | (intro x; simp [ii7mT,ii7mS,leaves]; omega)
def iii0nT : Tree := (.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 3) (.leaf 2))))))))))
def iii0nS : Tree := (.node ((.node ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 2))) (.leaf 1))
theorem iii0n_guards : (rawPlan iii0nT iii0nS 0 1 2 [true,true,true,false,false] [true] [true,true,true,false,true] [true,true,true,true,true]).all (currentGuard iii0nT iii0nS) = true := by decide
theorem iii0n_costs : (rawPlan iii0nT iii0nS 0 1 2 [true,true,true,false,false] [true] [true,true,true,false,true] [true,true,true,true,true]).map paid = [2,1,2] := by decide
theorem iii0n_cover (F : List (List Nat)) (ha : agreement iii0nT iii0nS F = true) : ∃ child, child ∈ rawPlan iii0nT iii0nS 0 1 2 [true,true,true,false,false] [true] [true,true,true,false,true] [true,true,true,true,true] ∧ OriginalCover iii0nT iii0nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,true,true,false]) (sa := false) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [iii0nT,iii0nS,leaves]; omega)
def iii0mT : Tree := (.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 7))) (.leaf 5))) (.leaf 6))
def iii0mS : Tree := (.node ((.node ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 2))) (.leaf 1))
theorem iii0m_guards : (rawPlan iii0mT iii0mS 0 1 2 [false,false,false,true,true] [true] [false,false,false,true,false] [false,false,false,false,false]).all (currentGuard iii0mT iii0mS) = true := by decide
theorem iii0m_costs : (rawPlan iii0mT iii0mS 0 1 2 [false,false,false,true,true] [true] [false,false,false,true,false] [false,false,false,false,false]).map paid = [2,1,2] := by decide
theorem iii0m_cover (F : List (List Nat)) (ha : agreement iii0mT iii0mS F = true) : ∃ child, child ∈ rawPlan iii0mT iii0mS 0 1 2 [false,false,false,true,true] [true] [false,false,false,true,false] [false,false,false,false,false] ∧ OriginalCover iii0mT iii0mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,false,false,true]) (sa := false) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [iii0mT,iii0mS,leaves]; omega)
def iii1nT : Tree := (.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 3) (.leaf 2))))))))))
def iii1nS : Tree := (.node ((.node ((.node ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (.leaf 0))) (.leaf 2))) (.leaf 1))
theorem iii1n_guards : (rawPlan iii1nT iii1nS 0 1 2 [true,true,true,false,false] [true] [true,true,true,false,true] [true,true,true,true,true]).all (currentGuard iii1nT iii1nS) = true := by decide
theorem iii1n_costs : (rawPlan iii1nT iii1nS 0 1 2 [true,true,true,false,false] [true] [true,true,true,false,true] [true,true,true,true,true]).map paid = [2,1,2] := by decide
theorem iii1n_cover (F : List (List Nat)) (ha : agreement iii1nT iii1nS F = true) : ∃ child, child ∈ rawPlan iii1nT iii1nS 0 1 2 [true,true,true,false,false] [true] [true,true,true,false,true] [true,true,true,true,true] ∧ OriginalCover iii1nT iii1nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,true,true,false]) (sa := true) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [iii1nT,iii1nS,leaves]; omega)
def iii1mT : Tree := (.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 7))) (.leaf 5))) (.leaf 6))
def iii1mS : Tree := (.node ((.node ((.node ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (.leaf 0))) (.leaf 2))) (.leaf 1))
theorem iii1m_guards : (rawPlan iii1mT iii1mS 0 1 2 [false,false,false,true,true] [true] [false,false,false,true,false] [false,false,false,false,false]).all (currentGuard iii1mT iii1mS) = true := by decide
theorem iii1m_costs : (rawPlan iii1mT iii1mS 0 1 2 [false,false,false,true,true] [true] [false,false,false,true,false] [false,false,false,false,false]).map paid = [2,1,2] := by decide
theorem iii1m_cover (F : List (List Nat)) (ha : agreement iii1mT iii1mS F = true) : ∃ child, child ∈ rawPlan iii1mT iii1mS 0 1 2 [false,false,false,true,true] [true] [false,false,false,true,false] [false,false,false,false,false] ∧ OriginalCover iii1mT iii1mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,false,false,true]) (sa := true) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [iii1mT,iii1mS,leaves]; omega)
def iii2nT : Tree := (.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 3) (.leaf 2))))))))))
def iii2nS : Tree := (.node ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))) (.leaf 1))
theorem iii2n_guards : (rawPlan iii2nT iii2nS 0 1 2 [true,true,true,false,false] [true] [true,true,true,false,true] [true,true,true,true,true]).all (currentGuard iii2nT iii2nS) = true := by decide
theorem iii2n_costs : (rawPlan iii2nT iii2nS 0 1 2 [true,true,true,false,false] [true] [true,true,true,false,true] [true,true,true,true,true]).map paid = [2,1,2] := by decide
theorem iii2n_cover (F : List (List Nat)) (ha : agreement iii2nT iii2nS F = true) : ∃ child, child ∈ rawPlan iii2nT iii2nS 0 1 2 [true,true,true,false,false] [true] [true,true,true,false,true] [true,true,true,true,true] ∧ OriginalCover iii2nT iii2nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,true,true,false]) (sa := false) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [iii2nT,iii2nS,leaves]; omega)
def iii2mT : Tree := (.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 7))) (.leaf 5))) (.leaf 6))
def iii2mS : Tree := (.node ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))) (.leaf 1))
theorem iii2m_guards : (rawPlan iii2mT iii2mS 0 1 2 [false,false,false,true,true] [true] [false,false,false,true,false] [false,false,false,false,false]).all (currentGuard iii2mT iii2mS) = true := by decide
theorem iii2m_costs : (rawPlan iii2mT iii2mS 0 1 2 [false,false,false,true,true] [true] [false,false,false,true,false] [false,false,false,false,false]).map paid = [2,1,2] := by decide
theorem iii2m_cover (F : List (List Nat)) (ha : agreement iii2mT iii2mS F = true) : ∃ child, child ∈ rawPlan iii2mT iii2mS 0 1 2 [false,false,false,true,true] [true] [false,false,false,true,false] [false,false,false,false,false] ∧ OriginalCover iii2mT iii2mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,false,false,true]) (sa := false) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [iii2mT,iii2mS,leaves]; omega)
def iii3nT : Tree := (.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 3) (.leaf 2))))))))))
def iii3nS : Tree := (.node ((.node (.leaf 2) ((.node ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (.leaf 0))))) (.leaf 1))
theorem iii3n_guards : (rawPlan iii3nT iii3nS 0 1 2 [true,true,true,false,false] [true] [true,true,true,false,true] [true,true,true,true,true]).all (currentGuard iii3nT iii3nS) = true := by decide
theorem iii3n_costs : (rawPlan iii3nT iii3nS 0 1 2 [true,true,true,false,false] [true] [true,true,true,false,true] [true,true,true,true,true]).map paid = [2,1,2] := by decide
theorem iii3n_cover (F : List (List Nat)) (ha : agreement iii3nT iii3nS F = true) : ∃ child, child ∈ rawPlan iii3nT iii3nS 0 1 2 [true,true,true,false,false] [true] [true,true,true,false,true] [true,true,true,true,true] ∧ OriginalCover iii3nT iii3nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,true,true,false]) (sa := true) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [iii3nT,iii3nS,leaves]; omega)
def iii3mT : Tree := (.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 7))) (.leaf 5))) (.leaf 6))
def iii3mS : Tree := (.node ((.node (.leaf 2) ((.node ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (.leaf 0))))) (.leaf 1))
theorem iii3m_guards : (rawPlan iii3mT iii3mS 0 1 2 [false,false,false,true,true] [true] [false,false,false,true,false] [false,false,false,false,false]).all (currentGuard iii3mT iii3mS) = true := by decide
theorem iii3m_costs : (rawPlan iii3mT iii3mS 0 1 2 [false,false,false,true,true] [true] [false,false,false,true,false] [false,false,false,false,false]).map paid = [2,1,2] := by decide
theorem iii3m_cover (F : List (List Nat)) (ha : agreement iii3mT iii3mS F = true) : ∃ child, child ∈ rawPlan iii3mT iii3mS 0 1 2 [false,false,false,true,true] [true] [false,false,false,true,false] [false,false,false,false,false] ∧ OriginalCover iii3mT iii3mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,false,false,true]) (sa := true) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [iii3mT,iii3mS,leaves]; omega)
def iii4nT : Tree := (.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 3) (.leaf 2))))))))))
def iii4nS : Tree := (.node (.leaf 1) ((.node ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 2))))
theorem iii4n_guards : (rawPlan iii4nT iii4nS 0 1 2 [true,true,true,false,false] [false] [true,true,true,false,true] [true,true,true,true,true]).all (currentGuard iii4nT iii4nS) = true := by decide
theorem iii4n_costs : (rawPlan iii4nT iii4nS 0 1 2 [true,true,true,false,false] [false] [true,true,true,false,true] [true,true,true,true,true]).map paid = [2,1,2] := by decide
theorem iii4n_cover (F : List (List Nat)) (ha : agreement iii4nT iii4nS F = true) : ∃ child, child ∈ rawPlan iii4nT iii4nS 0 1 2 [true,true,true,false,false] [false] [true,true,true,false,true] [true,true,true,true,true] ∧ OriginalCover iii4nT iii4nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,true,true,false]) (sa := false) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [iii4nT,iii4nS,leaves]; omega)
def iii4mT : Tree := (.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 7))) (.leaf 5))) (.leaf 6))
def iii4mS : Tree := (.node (.leaf 1) ((.node ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 2))))
theorem iii4m_guards : (rawPlan iii4mT iii4mS 0 1 2 [false,false,false,true,true] [false] [false,false,false,true,false] [false,false,false,false,false]).all (currentGuard iii4mT iii4mS) = true := by decide
theorem iii4m_costs : (rawPlan iii4mT iii4mS 0 1 2 [false,false,false,true,true] [false] [false,false,false,true,false] [false,false,false,false,false]).map paid = [2,1,2] := by decide
theorem iii4m_cover (F : List (List Nat)) (ha : agreement iii4mT iii4mS F = true) : ∃ child, child ∈ rawPlan iii4mT iii4mS 0 1 2 [false,false,false,true,true] [false] [false,false,false,true,false] [false,false,false,false,false] ∧ OriginalCover iii4mT iii4mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,false,false,true]) (sa := false) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [iii4mT,iii4mS,leaves]; omega)
def iii5nT : Tree := (.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 3) (.leaf 2))))))))))
def iii5nS : Tree := (.node (.leaf 1) ((.node ((.node ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (.leaf 0))) (.leaf 2))))
theorem iii5n_guards : (rawPlan iii5nT iii5nS 0 1 2 [true,true,true,false,false] [false] [true,true,true,false,true] [true,true,true,true,true]).all (currentGuard iii5nT iii5nS) = true := by decide
theorem iii5n_costs : (rawPlan iii5nT iii5nS 0 1 2 [true,true,true,false,false] [false] [true,true,true,false,true] [true,true,true,true,true]).map paid = [2,1,2] := by decide
theorem iii5n_cover (F : List (List Nat)) (ha : agreement iii5nT iii5nS F = true) : ∃ child, child ∈ rawPlan iii5nT iii5nS 0 1 2 [true,true,true,false,false] [false] [true,true,true,false,true] [true,true,true,true,true] ∧ OriginalCover iii5nT iii5nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,true,true,false]) (sa := true) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [iii5nT,iii5nS,leaves]; omega)
def iii5mT : Tree := (.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 7))) (.leaf 5))) (.leaf 6))
def iii5mS : Tree := (.node (.leaf 1) ((.node ((.node ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (.leaf 0))) (.leaf 2))))
theorem iii5m_guards : (rawPlan iii5mT iii5mS 0 1 2 [false,false,false,true,true] [false] [false,false,false,true,false] [false,false,false,false,false]).all (currentGuard iii5mT iii5mS) = true := by decide
theorem iii5m_costs : (rawPlan iii5mT iii5mS 0 1 2 [false,false,false,true,true] [false] [false,false,false,true,false] [false,false,false,false,false]).map paid = [2,1,2] := by decide
theorem iii5m_cover (F : List (List Nat)) (ha : agreement iii5mT iii5mS F = true) : ∃ child, child ∈ rawPlan iii5mT iii5mS 0 1 2 [false,false,false,true,true] [false] [false,false,false,true,false] [false,false,false,false,false] ∧ OriginalCover iii5mT iii5mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,false,false,true]) (sa := true) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [iii5mT,iii5mS,leaves]; omega)
def iii6nT : Tree := (.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 3) (.leaf 2))))))))))
def iii6nS : Tree := (.node (.leaf 1) ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))))
theorem iii6n_guards : (rawPlan iii6nT iii6nS 0 1 2 [true,true,true,false,false] [false] [true,true,true,false,true] [true,true,true,true,true]).all (currentGuard iii6nT iii6nS) = true := by decide
theorem iii6n_costs : (rawPlan iii6nT iii6nS 0 1 2 [true,true,true,false,false] [false] [true,true,true,false,true] [true,true,true,true,true]).map paid = [2,1,2] := by decide
theorem iii6n_cover (F : List (List Nat)) (ha : agreement iii6nT iii6nS F = true) : ∃ child, child ∈ rawPlan iii6nT iii6nS 0 1 2 [true,true,true,false,false] [false] [true,true,true,false,true] [true,true,true,true,true] ∧ OriginalCover iii6nT iii6nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,true,true,false]) (sa := false) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [iii6nT,iii6nS,leaves]; omega)
def iii6mT : Tree := (.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 7))) (.leaf 5))) (.leaf 6))
def iii6mS : Tree := (.node (.leaf 1) ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))))
theorem iii6m_guards : (rawPlan iii6mT iii6mS 0 1 2 [false,false,false,true,true] [false] [false,false,false,true,false] [false,false,false,false,false]).all (currentGuard iii6mT iii6mS) = true := by decide
theorem iii6m_costs : (rawPlan iii6mT iii6mS 0 1 2 [false,false,false,true,true] [false] [false,false,false,true,false] [false,false,false,false,false]).map paid = [2,1,2] := by decide
theorem iii6m_cover (F : List (List Nat)) (ha : agreement iii6mT iii6mS F = true) : ∃ child, child ∈ rawPlan iii6mT iii6mS 0 1 2 [false,false,false,true,true] [false] [false,false,false,true,false] [false,false,false,false,false] ∧ OriginalCover iii6mT iii6mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,false,false,true]) (sa := false) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [iii6mT,iii6mS,leaves]; omega)
def iii7nT : Tree := (.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 3) (.leaf 2))))))))))
def iii7nS : Tree := (.node (.leaf 1) ((.node (.leaf 2) ((.node ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (.leaf 0))))))
theorem iii7n_guards : (rawPlan iii7nT iii7nS 0 1 2 [true,true,true,false,false] [false] [true,true,true,false,true] [true,true,true,true,true]).all (currentGuard iii7nT iii7nS) = true := by decide
theorem iii7n_costs : (rawPlan iii7nT iii7nS 0 1 2 [true,true,true,false,false] [false] [true,true,true,false,true] [true,true,true,true,true]).map paid = [2,1,2] := by decide
theorem iii7n_cover (F : List (List Nat)) (ha : agreement iii7nT iii7nS F = true) : ∃ child, child ∈ rawPlan iii7nT iii7nS 0 1 2 [true,true,true,false,false] [false] [true,true,true,false,true] [true,true,true,true,true] ∧ OriginalCover iii7nT iii7nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 0) (.leaf 1))) (w := []) (r := [true,true,true,false]) (sa := true) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [iii7nT,iii7nS,leaves]; omega)
def iii7mT : Tree := (.node ((.node ((.node ((.node ((.node (.leaf 2) (.leaf 3))) ((.node (.leaf 1) (.leaf 0))))) (.leaf 7))) (.leaf 5))) (.leaf 6))
def iii7mS : Tree := (.node (.leaf 1) ((.node (.leaf 2) ((.node ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (.leaf 0))))))
theorem iii7m_guards : (rawPlan iii7mT iii7mS 0 1 2 [false,false,false,true,true] [false] [false,false,false,true,false] [false,false,false,false,false]).all (currentGuard iii7mT iii7mS) = true := by decide
theorem iii7m_costs : (rawPlan iii7mT iii7mS 0 1 2 [false,false,false,true,true] [false] [false,false,false,true,false] [false,false,false,false,false]).map paid = [2,1,2] := by decide
theorem iii7m_cover (F : List (List Nat)) (ha : agreement iii7mT iii7mS F = true) : ∃ child, child ∈ rawPlan iii7mT iii7mS 0 1 2 [false,false,false,true,true] [false] [false,false,false,true,false] [false,false,false,false,false] ∧ OriginalCover iii7mT iii7mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))) (C := (.node (.leaf 1) (.leaf 0))) (w := []) (r := [false,false,false,true]) (sa := true) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[false,false,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [iii7mT,iii7mS,leaves]; omega)
def core0nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def core0nS : Tree := (.node ((.node ((.node ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))) (.leaf 2))) (.leaf 1))) (.leaf 10))
theorem core0n_guards : (rawPlan core0nT core0nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true]).all (currentGuard core0nT core0nS) = true := by decide
theorem core0n_costs : (rawPlan core0nT core0nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true]).map paid = [2,1,4] := by decide
theorem core0n_cover (F : List (List Nat)) (ha : agreement core0nT core0nS F = true) : ∃ child, child ∈ rawPlan core0nT core0nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true] ∧ OriginalCover core0nT core0nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))) (w := [false]) (r := [false,false,false,true]) (sa := false) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[false,false,false,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [core0nT,core0nS,leaves]; omega)
def core0mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (.leaf 5))))))))
def core0mS : Tree := (.node ((.node ((.node ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))) (.leaf 2))) (.leaf 1))) (.leaf 10))
theorem core0m_guards : (rawPlan core0mT core0mS 0 1 2 [true,true,true,false,true,true] [false,true] [true,true,true,false,true,false] [true,false]).all (currentGuard core0mT core0mS) = true := by decide
theorem core0m_costs : (rawPlan core0mT core0mS 0 1 2 [true,true,true,false,true,true] [false,true] [true,true,true,false,true,false] [true,false]).map paid = [2,1,4] := by decide
theorem core0m_cover (F : List (List Nat)) (ha : agreement core0mT core0mS F = true) : ∃ child, child ∈ rawPlan core0mT core0mS 0 1 2 [true,true,true,false,true,true] [false,true] [true,true,true,false,true,false] [true,false] ∧ OriginalCover core0mT core0mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (w := [false]) (r := [true,true,true,false]) (sa := false) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[true,true,true,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [core0mT,core0mS,leaves]; omega)
def core1nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def core1nS : Tree := (.node ((.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))) (.leaf 2))) (.leaf 1))) (.leaf 10))
theorem core1n_guards : (rawPlan core1nT core1nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true]).all (currentGuard core1nT core1nS) = true := by decide
theorem core1n_costs : (rawPlan core1nT core1nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true]).map paid = [2,1,4] := by decide
theorem core1n_cover (F : List (List Nat)) (ha : agreement core1nT core1nS F = true) : ∃ child, child ∈ rawPlan core1nT core1nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true] ∧ OriginalCover core1nT core1nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))) (w := [false]) (r := [false,false,false,true]) (sa := true) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[false,false,false,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [core1nT,core1nS,leaves]; omega)
def core1mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (.leaf 5))))))))
def core1mS : Tree := (.node ((.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))) (.leaf 2))) (.leaf 1))) (.leaf 10))
theorem core1m_guards : (rawPlan core1mT core1mS 0 1 2 [true,true,true,false,true,true] [false,true] [true,true,true,false,true,false] [true,false]).all (currentGuard core1mT core1mS) = true := by decide
theorem core1m_costs : (rawPlan core1mT core1mS 0 1 2 [true,true,true,false,true,true] [false,true] [true,true,true,false,true,false] [true,false]).map paid = [2,1,4] := by decide
theorem core1m_cover (F : List (List Nat)) (ha : agreement core1mT core1mS F = true) : ∃ child, child ∈ rawPlan core1mT core1mS 0 1 2 [true,true,true,false,true,true] [false,true] [true,true,true,false,true,false] [true,false] ∧ OriginalCover core1mT core1mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (w := [false]) (r := [true,true,true,false]) (sa := true) (sc := false) (sb := false)
 all_goals first | exact ha | exact ⟨[true,true,true,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [core1mT,core1mS,leaves]; omega)
def core2nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def core2nS : Tree := (.node ((.node ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))))) (.leaf 1))) (.leaf 10))
theorem core2n_guards : (rawPlan core2nT core2nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true]).all (currentGuard core2nT core2nS) = true := by decide
theorem core2n_costs : (rawPlan core2nT core2nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true]).map paid = [2,1,4] := by decide
theorem core2n_cover (F : List (List Nat)) (ha : agreement core2nT core2nS F = true) : ∃ child, child ∈ rawPlan core2nT core2nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true] ∧ OriginalCover core2nT core2nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))) (w := [false]) (r := [false,false,false,true]) (sa := false) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[false,false,false,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [core2nT,core2nS,leaves]; omega)
def core2mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (.leaf 5))))))))
def core2mS : Tree := (.node ((.node ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))))) (.leaf 1))) (.leaf 10))
theorem core2m_guards : (rawPlan core2mT core2mS 0 1 2 [true,true,true,false,true,true] [false,true] [true,true,true,false,true,false] [true,false]).all (currentGuard core2mT core2mS) = true := by decide
theorem core2m_costs : (rawPlan core2mT core2mS 0 1 2 [true,true,true,false,true,true] [false,true] [true,true,true,false,true,false] [true,false]).map paid = [2,1,4] := by decide
theorem core2m_cover (F : List (List Nat)) (ha : agreement core2mT core2mS F = true) : ∃ child, child ∈ rawPlan core2mT core2mS 0 1 2 [true,true,true,false,true,true] [false,true] [true,true,true,false,true,false] [true,false] ∧ OriginalCover core2mT core2mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (w := [false]) (r := [true,true,true,false]) (sa := false) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[true,true,true,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [core2mT,core2mS,leaves]; omega)
def core3nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def core3nS : Tree := (.node ((.node ((.node (.leaf 2) ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))))) (.leaf 1))) (.leaf 10))
theorem core3n_guards : (rawPlan core3nT core3nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true]).all (currentGuard core3nT core3nS) = true := by decide
theorem core3n_costs : (rawPlan core3nT core3nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true]).map paid = [2,1,4] := by decide
theorem core3n_cover (F : List (List Nat)) (ha : agreement core3nT core3nS F = true) : ∃ child, child ∈ rawPlan core3nT core3nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true] ∧ OriginalCover core3nT core3nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))) (w := [false]) (r := [false,false,false,true]) (sa := true) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[false,false,false,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [core3nT,core3nS,leaves]; omega)
def core3mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (.leaf 5))))))))
def core3mS : Tree := (.node ((.node ((.node (.leaf 2) ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))))) (.leaf 1))) (.leaf 10))
theorem core3m_guards : (rawPlan core3mT core3mS 0 1 2 [true,true,true,false,true,true] [false,true] [true,true,true,false,true,false] [true,false]).all (currentGuard core3mT core3mS) = true := by decide
theorem core3m_costs : (rawPlan core3mT core3mS 0 1 2 [true,true,true,false,true,true] [false,true] [true,true,true,false,true,false] [true,false]).map paid = [2,1,4] := by decide
theorem core3m_cover (F : List (List Nat)) (ha : agreement core3mT core3mS F = true) : ∃ child, child ∈ rawPlan core3mT core3mS 0 1 2 [true,true,true,false,true,true] [false,true] [true,true,true,false,true,false] [true,false] ∧ OriginalCover core3mT core3mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (w := [false]) (r := [true,true,true,false]) (sa := true) (sc := true) (sb := false)
 all_goals first | exact ha | exact ⟨[true,true,true,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [core3mT,core3mS,leaves]; omega)
def core4nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def core4nS : Tree := (.node ((.node (.leaf 1) ((.node ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))) (.leaf 2))))) (.leaf 10))
theorem core4n_guards : (rawPlan core4nT core4nS 0 1 2 [false,false,false,true,false,false] [false,false] [false,false,false,true,false,true] [false,true]).all (currentGuard core4nT core4nS) = true := by decide
theorem core4n_costs : (rawPlan core4nT core4nS 0 1 2 [false,false,false,true,false,false] [false,false] [false,false,false,true,false,true] [false,true]).map paid = [2,1,4] := by decide
theorem core4n_cover (F : List (List Nat)) (ha : agreement core4nT core4nS F = true) : ∃ child, child ∈ rawPlan core4nT core4nS 0 1 2 [false,false,false,true,false,false] [false,false] [false,false,false,true,false,true] [false,true] ∧ OriginalCover core4nT core4nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))) (w := [false]) (r := [false,false,false,true]) (sa := false) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[false,false,false,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [core4nT,core4nS,leaves]; omega)
def core4mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (.leaf 5))))))))
def core4mS : Tree := (.node ((.node (.leaf 1) ((.node ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))) (.leaf 2))))) (.leaf 10))
theorem core4m_guards : (rawPlan core4mT core4mS 0 1 2 [true,true,true,false,true,true] [false,false] [true,true,true,false,true,false] [true,false]).all (currentGuard core4mT core4mS) = true := by decide
theorem core4m_costs : (rawPlan core4mT core4mS 0 1 2 [true,true,true,false,true,true] [false,false] [true,true,true,false,true,false] [true,false]).map paid = [2,1,4] := by decide
theorem core4m_cover (F : List (List Nat)) (ha : agreement core4mT core4mS F = true) : ∃ child, child ∈ rawPlan core4mT core4mS 0 1 2 [true,true,true,false,true,true] [false,false] [true,true,true,false,true,false] [true,false] ∧ OriginalCover core4mT core4mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (w := [false]) (r := [true,true,true,false]) (sa := false) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[true,true,true,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [core4mT,core4mS,leaves]; omega)
def core5nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def core5nS : Tree := (.node ((.node (.leaf 1) ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))) (.leaf 2))))) (.leaf 10))
theorem core5n_guards : (rawPlan core5nT core5nS 0 1 2 [false,false,false,true,false,false] [false,false] [false,false,false,true,false,true] [false,true]).all (currentGuard core5nT core5nS) = true := by decide
theorem core5n_costs : (rawPlan core5nT core5nS 0 1 2 [false,false,false,true,false,false] [false,false] [false,false,false,true,false,true] [false,true]).map paid = [2,1,4] := by decide
theorem core5n_cover (F : List (List Nat)) (ha : agreement core5nT core5nS F = true) : ∃ child, child ∈ rawPlan core5nT core5nS 0 1 2 [false,false,false,true,false,false] [false,false] [false,false,false,true,false,true] [false,true] ∧ OriginalCover core5nT core5nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))) (w := [false]) (r := [false,false,false,true]) (sa := true) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[false,false,false,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [core5nT,core5nS,leaves]; omega)
def core5mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (.leaf 5))))))))
def core5mS : Tree := (.node ((.node (.leaf 1) ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))) (.leaf 2))))) (.leaf 10))
theorem core5m_guards : (rawPlan core5mT core5mS 0 1 2 [true,true,true,false,true,true] [false,false] [true,true,true,false,true,false] [true,false]).all (currentGuard core5mT core5mS) = true := by decide
theorem core5m_costs : (rawPlan core5mT core5mS 0 1 2 [true,true,true,false,true,true] [false,false] [true,true,true,false,true,false] [true,false]).map paid = [2,1,4] := by decide
theorem core5m_cover (F : List (List Nat)) (ha : agreement core5mT core5mS F = true) : ∃ child, child ∈ rawPlan core5mT core5mS 0 1 2 [true,true,true,false,true,true] [false,false] [true,true,true,false,true,false] [true,false] ∧ OriginalCover core5mT core5mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (w := [false]) (r := [true,true,true,false]) (sa := true) (sc := false) (sb := true)
 all_goals first | exact ha | exact ⟨[true,true,true,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [core5mT,core5mS,leaves]; omega)
def core6nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def core6nS : Tree := (.node ((.node (.leaf 1) ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))))))) (.leaf 10))
theorem core6n_guards : (rawPlan core6nT core6nS 0 1 2 [false,false,false,true,false,false] [false,false] [false,false,false,true,false,true] [false,true]).all (currentGuard core6nT core6nS) = true := by decide
theorem core6n_costs : (rawPlan core6nT core6nS 0 1 2 [false,false,false,true,false,false] [false,false] [false,false,false,true,false,true] [false,true]).map paid = [2,1,4] := by decide
theorem core6n_cover (F : List (List Nat)) (ha : agreement core6nT core6nS F = true) : ∃ child, child ∈ rawPlan core6nT core6nS 0 1 2 [false,false,false,true,false,false] [false,false] [false,false,false,true,false,true] [false,true] ∧ OriginalCover core6nT core6nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))) (w := [false]) (r := [false,false,false,true]) (sa := false) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[false,false,false,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [core6nT,core6nS,leaves]; omega)
def core6mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (.leaf 5))))))))
def core6mS : Tree := (.node ((.node (.leaf 1) ((.node (.leaf 2) ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))))))) (.leaf 10))
theorem core6m_guards : (rawPlan core6mT core6mS 0 1 2 [true,true,true,false,true,true] [false,false] [true,true,true,false,true,false] [true,false]).all (currentGuard core6mT core6mS) = true := by decide
theorem core6m_costs : (rawPlan core6mT core6mS 0 1 2 [true,true,true,false,true,true] [false,false] [true,true,true,false,true,false] [true,false]).map paid = [2,1,4] := by decide
theorem core6m_cover (F : List (List Nat)) (ha : agreement core6mT core6mS F = true) : ∃ child, child ∈ rawPlan core6mT core6mS 0 1 2 [true,true,true,false,true,true] [false,false] [true,true,true,false,true,false] [true,false] ∧ OriginalCover core6mT core6mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (w := [false]) (r := [true,true,true,false]) (sa := false) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[true,true,true,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [core6mT,core6mS,leaves]; omega)
def core7nT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def core7nS : Tree := (.node ((.node (.leaf 1) ((.node (.leaf 2) ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))))))) (.leaf 10))
theorem core7n_guards : (rawPlan core7nT core7nS 0 1 2 [false,false,false,true,false,false] [false,false] [false,false,false,true,false,true] [false,true]).all (currentGuard core7nT core7nS) = true := by decide
theorem core7n_costs : (rawPlan core7nT core7nS 0 1 2 [false,false,false,true,false,false] [false,false] [false,false,false,true,false,true] [false,true]).map paid = [2,1,4] := by decide
theorem core7n_cover (F : List (List Nat)) (ha : agreement core7nT core7nS F = true) : ∃ child, child ∈ rawPlan core7nT core7nS 0 1 2 [false,false,false,true,false,false] [false,false] [false,false,false,true,false,true] [false,true] ∧ OriginalCover core7nT core7nS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node ((.node (.leaf 0) (.leaf 1))) (.leaf 10))) (w := [false]) (r := [false,false,false,true]) (sa := true) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[false,false,false,true,false],Or.inl rfl⟩ | rfl | decide | (intro x; simp [core7nT,core7nS,leaves]; omega)
def core7mT : Tree := (.node (.leaf 9) ((.node (.leaf 2) ((.node (.leaf 8) ((.node ((.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (.leaf 5))))))))
def core7mS : Tree := (.node ((.node (.leaf 1) ((.node (.leaf 2) ((.node ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (.leaf 0))))))) (.leaf 10))
theorem core7m_guards : (rawPlan core7mT core7mS 0 1 2 [true,true,true,false,true,true] [false,false] [true,true,true,false,true,false] [true,false]).all (currentGuard core7mT core7mS) = true := by decide
theorem core7m_costs : (rawPlan core7mT core7mS 0 1 2 [true,true,true,false,true,true] [false,false] [true,true,true,false,true,false] [true,false]).map paid = [2,1,4] := by decide
theorem core7m_cover (F : List (List Nat)) (ha : agreement core7mT core7mS F = true) : ∃ child, child ∈ rawPlan core7mT core7mS 0 1 2 [true,true,true,false,true,true] [false,false] [true,true,true,false,true,false] [true,false] ∧ OriginalCover core7mT core7mS F child.partition := by
 apply rawPlan_original_cover (X := (.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))) (C := (.node (.leaf 10) ((.node (.leaf 1) (.leaf 0))))) (w := [false]) (r := [true,true,true,false]) (sa := true) (sc := true) (sb := true)
 all_goals first | exact ha | exact ⟨[true,true,true,false,true],Or.inr rfl⟩ | rfl | decide | (intro x; simp [core7mT,core7mS,leaves]; omega)
def falseBindingT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 0) (.leaf 1))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def falseBindingS : Tree := (.node ((.node ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))) (.leaf 2))) (.leaf 1))
theorem clean_b_binding : currentGuard falseBindingT falseBindingS (bBranch falseBindingS 1 [true]) = true := by decide
theorem corrupt_c_for_b_binding : currentGuard falseBindingT falseBindingS (bBranch falseBindingS 1 [false,true]) = false := by decide
theorem corrupt_role_is_different : current falseBindingS falseBindingT (bBranch falseBindingS 1 [true]) ≠ current falseBindingT falseBindingS (bBranch falseBindingS 1 [true]) := by decide
end Universal233.Case322Extraction.Controls
