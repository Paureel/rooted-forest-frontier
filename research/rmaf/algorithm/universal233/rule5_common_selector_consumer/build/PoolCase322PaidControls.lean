import PaidCaller
namespace Universal233.Case322PaidGuard.Controls
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322 Universal233.Case322Extraction Universal233.Case322PaidGuard
set_option maxRecDepth 26000
def i0T : Tree := (.node (.leaf 4) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 6) (.node (.leaf 5) (.node (.leaf 7) (.node (.leaf 3) (.leaf 2)))))))
def i0S : Tree := (.node (.node (.node (.leaf 0) (.node (.leaf 3) (.node (.leaf 4) (.node (.leaf 5) (.node (.leaf 6) (.leaf 7)))))) (.leaf 2)) (.leaf 1))
def i0 : LiteralGeometry i0T i0S where
 X := (.node (.leaf 3) (.node (.leaf 4) (.node (.leaf 5) (.node (.leaf 6) (.leaf 7)))))
 C := (.node (.leaf 0) (.leaf 1))
 w := []
 r := [true,false]
 qa := [true,false,false]
 ub := [true,false,true]
 uc := [true,true,true,true,true,true]
 sa := false
 sc := false
 sb := false
 a := 0
 b := 1
 c := 2
 properT := by decide
 properS := by decide
 same := by intro x; simp [i0T,i0S,leaves]; omega
 source := rfl
 cherry := ⟨[true,false],Or.inl rfl⟩
 two := by decide
 core := rfl
 coreLabels := by intro x hx; simp [i0T,leaves] at hx ⊢; omega
 bC := by decide
 cC := by decide
 leafA := rfl
 leafB := rfl
 leafC := rfl
 frontier := Or.inl (by decide)
 tailR := by decide
 tailC := by decide
 offR := by decide
 offC := by decide
theorem i0_allGuards : ∀ child, child ∈ literalPlan i0 → currentGuard i0T i0S child = true := literalPlan_guards i0
theorem i0_costs : (guardedPlan i0).map paid = [2,1,2,2] := by decide
theorem i0_swapGuards : ∀ child, child ∈ swappedGuardedPlan i0 → currentGuard i0S i0T child = true := swapped_guarded_binding i0
def i7T : Tree := (.node (.node (.node (.node (.node (.node (.leaf 2) (.leaf 3)) (.leaf 7)) (.leaf 5)) (.leaf 6)) (.node (.leaf 1) (.leaf 0))) (.leaf 4))
def i7S : Tree := (.node (.leaf 1) (.node (.leaf 2) (.node (.node (.leaf 3) (.node (.leaf 4) (.node (.leaf 5) (.node (.leaf 6) (.leaf 7))))) (.leaf 0))))
def i7 : LiteralGeometry i7T i7S where
 X := (.node (.leaf 3) (.node (.leaf 4) (.node (.leaf 5) (.node (.leaf 6) (.leaf 7)))))
 C := (.node (.leaf 1) (.leaf 0))
 w := []
 r := [false,true]
 qa := [false,true,true]
 ub := [false,true,false]
 uc := [false,false,false,false,false,false]
 sa := true
 sc := true
 sb := true
 a := 0
 b := 1
 c := 2
 properT := by decide
 properS := by decide
 same := by intro x; simp [i7T,i7S,leaves]; omega
 source := rfl
 cherry := ⟨[false,true],Or.inr rfl⟩
 two := by decide
 core := rfl
 coreLabels := by intro x hx; simp [i7T,leaves] at hx ⊢; omega
 bC := by decide
 cC := by decide
 leafA := rfl
 leafB := rfl
 leafC := rfl
 frontier := Or.inr (by decide)
 tailR := by decide
 tailC := by decide
 offR := by decide
 offC := by decide
theorem i7_allGuards : ∀ child, child ∈ literalPlan i7 → currentGuard i7T i7S child = true := literalPlan_guards i7
theorem i7_costs : (guardedPlan i7).map paid = [2,1,2,2] := by decide
theorem i7_swapGuards : ∀ child, child ∈ swappedGuardedPlan i7 → currentGuard i7S i7T child = true := swapped_guarded_binding i7
def ii0T : Tree := (.node (.node (.node (.node (.leaf 5) (.node (.leaf 0) (.leaf 1))) (.leaf 8)) (.leaf 2)) (.leaf 9))
def ii0S : Tree := (.node (.node (.node (.leaf 0) (.node (.leaf 5) (.node (.leaf 8) (.leaf 9)))) (.leaf 2)) (.leaf 1))
def ii0 : LiteralGeometry ii0T ii0S where
 X := (.node (.leaf 5) (.node (.leaf 8) (.leaf 9)))
 C := (.node (.leaf 0) (.leaf 1))
 w := []
 r := [false,false,false,true]
 qa := [false,false,false,true,false]
 ub := [false,false,false,true,true]
 uc := [false,true]
 sa := false
 sc := false
 sb := false
 a := 0
 b := 1
 c := 2
 properT := by decide
 properS := by decide
 same := by intro x; simp [ii0T,ii0S,leaves]; omega
 source := rfl
 cherry := ⟨[false,false,false,true],Or.inl rfl⟩
 two := by decide
 core := rfl
 coreLabels := by intro x hx; simp [ii0T,leaves] at hx ⊢; omega
 bC := by decide
 cC := by decide
 leafA := rfl
 leafB := rfl
 leafC := rfl
 frontier := Or.inl (by decide)
 tailR := by decide
 tailC := by decide
 offR := by decide
 offC := by decide
theorem ii0_allGuards : ∀ child, child ∈ literalPlan ii0 → currentGuard ii0T ii0S child = true := literalPlan_guards ii0
theorem ii0_costs : (guardedPlan ii0).map paid = [2,1,3] := by decide
theorem ii0_swapGuards : ∀ child, child ∈ swappedGuardedPlan ii0 → currentGuard ii0S ii0T child = true := swapped_guarded_binding ii0
def ii7T : Tree := (.node (.leaf 9) (.node (.leaf 2) (.node (.leaf 8) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 5)))))
def ii7S : Tree := (.node (.leaf 1) (.node (.leaf 2) (.node (.node (.leaf 5) (.node (.leaf 8) (.leaf 9))) (.leaf 0))))
def ii7 : LiteralGeometry ii7T ii7S where
 X := (.node (.leaf 5) (.node (.leaf 8) (.leaf 9)))
 C := (.node (.leaf 1) (.leaf 0))
 w := []
 r := [true,true,true,false]
 qa := [true,true,true,false,true]
 ub := [true,true,true,false,false]
 uc := [true,false]
 sa := true
 sc := true
 sb := true
 a := 0
 b := 1
 c := 2
 properT := by decide
 properS := by decide
 same := by intro x; simp [ii7T,ii7S,leaves]; omega
 source := rfl
 cherry := ⟨[true,true,true,false],Or.inr rfl⟩
 two := by decide
 core := rfl
 coreLabels := by intro x hx; simp [ii7T,leaves] at hx ⊢; omega
 bC := by decide
 cC := by decide
 leafA := rfl
 leafB := rfl
 leafC := rfl
 frontier := Or.inr (by decide)
 tailR := by decide
 tailC := by decide
 offR := by decide
 offC := by decide
theorem ii7_allGuards : ∀ child, child ∈ literalPlan ii7 → currentGuard ii7T ii7S child = true := literalPlan_guards ii7
theorem ii7_costs : (guardedPlan ii7).map paid = [2,1,3] := by decide
theorem ii7_swapGuards : ∀ child, child ∈ swappedGuardedPlan ii7 → currentGuard ii7S ii7T child = true := swapped_guarded_binding ii7
def iii0T : Tree := (.node (.leaf 6) (.node (.leaf 5) (.node (.leaf 7) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 3) (.leaf 2))))))
def iii0S : Tree := (.node (.node (.node (.leaf 0) (.node (.leaf 3) (.node (.leaf 5) (.node (.leaf 6) (.leaf 7))))) (.leaf 2)) (.leaf 1))
def iii0 : LiteralGeometry iii0T iii0S where
 X := (.node (.leaf 3) (.node (.leaf 5) (.node (.leaf 6) (.leaf 7))))
 C := (.node (.leaf 0) (.leaf 1))
 w := []
 r := [true,true,true,false]
 qa := [true,true,true,false,false]
 ub := [true,true,true,false,true]
 uc := [true,true,true,true,true]
 sa := false
 sc := false
 sb := false
 a := 0
 b := 1
 c := 2
 properT := by decide
 properS := by decide
 same := by intro x; simp [iii0T,iii0S,leaves]; omega
 source := rfl
 cherry := ⟨[true,true,true,false],Or.inl rfl⟩
 two := by decide
 core := rfl
 coreLabels := by intro x hx; simp [iii0T,leaves] at hx ⊢; omega
 bC := by decide
 cC := by decide
 leafA := rfl
 leafB := rfl
 leafC := rfl
 frontier := Or.inl (by decide)
 tailR := by decide
 tailC := by decide
 offR := by decide
 offC := by decide
theorem iii0_allGuards : ∀ child, child ∈ literalPlan iii0 → currentGuard iii0T iii0S child = true := literalPlan_guards iii0
theorem iii0_costs : (guardedPlan iii0).map paid = [2,1,2] := by decide
theorem iii0_swapGuards : ∀ child, child ∈ swappedGuardedPlan iii0 → currentGuard iii0S iii0T child = true := swapped_guarded_binding iii0
def iii7T : Tree := (.node (.node (.node (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 1) (.leaf 0))) (.leaf 7)) (.leaf 5)) (.leaf 6))
def iii7S : Tree := (.node (.leaf 1) (.node (.leaf 2) (.node (.node (.leaf 3) (.node (.leaf 5) (.node (.leaf 6) (.leaf 7)))) (.leaf 0))))
def iii7 : LiteralGeometry iii7T iii7S where
 X := (.node (.leaf 3) (.node (.leaf 5) (.node (.leaf 6) (.leaf 7))))
 C := (.node (.leaf 1) (.leaf 0))
 w := []
 r := [false,false,false,true]
 qa := [false,false,false,true,true]
 ub := [false,false,false,true,false]
 uc := [false,false,false,false,false]
 sa := true
 sc := true
 sb := true
 a := 0
 b := 1
 c := 2
 properT := by decide
 properS := by decide
 same := by intro x; simp [iii7T,iii7S,leaves]; omega
 source := rfl
 cherry := ⟨[false,false,false,true],Or.inr rfl⟩
 two := by decide
 core := rfl
 coreLabels := by intro x hx; simp [iii7T,leaves] at hx ⊢; omega
 bC := by decide
 cC := by decide
 leafA := rfl
 leafB := rfl
 leafC := rfl
 frontier := Or.inr (by decide)
 tailR := by decide
 tailC := by decide
 offR := by decide
 offC := by decide
theorem iii7_allGuards : ∀ child, child ∈ literalPlan iii7 → currentGuard iii7T iii7S child = true := literalPlan_guards iii7
theorem iii7_costs : (guardedPlan iii7).map paid = [2,1,2] := by decide
theorem iii7_swapGuards : ∀ child, child ∈ swappedGuardedPlan iii7 → currentGuard iii7S iii7T child = true := swapped_guarded_binding iii7
def core0T : Tree := (.node (.node (.node (.node (.leaf 5) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 10))) (.leaf 8)) (.leaf 2)) (.leaf 9))
def core0S : Tree := (.node (.node (.node (.node (.leaf 0) (.node (.leaf 5) (.node (.leaf 8) (.leaf 9)))) (.leaf 2)) (.leaf 1)) (.leaf 10))
def core0 : LiteralGeometry core0T core0S where
 X := (.node (.leaf 5) (.node (.leaf 8) (.leaf 9)))
 C := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 10))
 w := [false]
 r := [false,false,false,true]
 qa := [false,false,false,true,false,false]
 ub := [false,false,false,true,false,true]
 uc := [false,true]
 sa := false
 sc := false
 sb := false
 a := 0
 b := 1
 c := 2
 properT := by decide
 properS := by decide
 same := by intro x; simp [core0T,core0S,leaves]; omega
 source := rfl
 cherry := ⟨[false,false,false,true,false],Or.inl rfl⟩
 two := by decide
 core := rfl
 coreLabels := by intro x hx; simp [core0T,leaves] at hx ⊢; omega
 bC := by decide
 cC := by decide
 leafA := rfl
 leafB := rfl
 leafC := rfl
 frontier := Or.inl (by decide)
 tailR := by decide
 tailC := by decide
 offR := by decide
 offC := by decide
theorem core0_allGuards : ∀ child, child ∈ literalPlan core0 → currentGuard core0T core0S child = true := literalPlan_guards core0
theorem core0_costs : (guardedPlan core0).map paid = [2,1,4] := by decide
theorem core0_swapGuards : ∀ child, child ∈ swappedGuardedPlan core0 → currentGuard core0S core0T child = true := swapped_guarded_binding core0
def core7T : Tree := (.node (.leaf 9) (.node (.leaf 2) (.node (.leaf 8) (.node (.node (.leaf 10) (.node (.leaf 1) (.leaf 0))) (.leaf 5)))))
def core7S : Tree := (.node (.node (.leaf 1) (.node (.leaf 2) (.node (.node (.leaf 5) (.node (.leaf 8) (.leaf 9))) (.leaf 0)))) (.leaf 10))
def core7 : LiteralGeometry core7T core7S where
 X := (.node (.leaf 5) (.node (.leaf 8) (.leaf 9)))
 C := (.node (.leaf 10) (.node (.leaf 1) (.leaf 0)))
 w := [false]
 r := [true,true,true,false]
 qa := [true,true,true,false,true,true]
 ub := [true,true,true,false,true,false]
 uc := [true,false]
 sa := true
 sc := true
 sb := true
 a := 0
 b := 1
 c := 2
 properT := by decide
 properS := by decide
 same := by intro x; simp [core7T,core7S,leaves]; omega
 source := rfl
 cherry := ⟨[true,true,true,false,true],Or.inr rfl⟩
 two := by decide
 core := rfl
 coreLabels := by intro x hx; simp [core7T,leaves] at hx ⊢; omega
 bC := by decide
 cC := by decide
 leafA := rfl
 leafB := rfl
 leafC := rfl
 frontier := Or.inr (by decide)
 tailR := by decide
 tailC := by decide
 offR := by decide
 offC := by decide
theorem core7_allGuards : ∀ child, child ∈ literalPlan core7 → currentGuard core7T core7S child = true := literalPlan_guards core7
theorem core7_costs : (guardedPlan core7).map paid = [2,1,4] := by decide
theorem core7_swapGuards : ∀ child, child ∈ swappedGuardedPlan core7 → currentGuard core7S core7T child = true := swapped_guarded_binding core7
end Universal233.Case322PaidGuard.Controls
