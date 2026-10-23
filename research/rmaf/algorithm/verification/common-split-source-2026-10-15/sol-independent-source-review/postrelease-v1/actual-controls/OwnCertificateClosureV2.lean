import OwnReadout
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase00
def t : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
def s : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
def tx : Tree := (.node (.leaf 0) (.leaf 1))
def sx : Tree := (.node (.leaf 0) (.leaf 1))
def ty : Tree := (.node (.leaf 2) (.leaf 3))
def sy : Tree := (.node (.leaf 2) (.leaf 3))
def mxt : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 100))
def mxs : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 100))
def myt : Tree := (.node (.leaf 101) (.node (.leaf 2) (.leaf 3)))
def mys : Tree := (.node (.leaf 101) (.node (.leaf 2) (.leaf 3)))
def xs : List Nat := [0,1]
def ys : List Nat := [2,3]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 0) (.leaf 1)),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.node (.leaf 0) (.leaf 1)),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 0 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 2 100 101 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase00
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase01
def t : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
def s : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))
def tx : Tree := (.node (.leaf 0) (.leaf 1))
def sx : Tree := (.node (.leaf 0) (.leaf 1))
def ty : Tree := (.leaf 2)
def sy : Tree := (.leaf 2)
def mxt : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 100))
def mxs : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 100)))
def myt : Tree := (.node (.leaf 101) (.leaf 2))
def mys : Tree := (.node (.leaf 101) (.leaf 2))
def xs : List Nat := [0,1]
def ys : List Nat := [2]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 0) (.leaf 1)),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[true,true],(.leaf 2),by decide,by decide,Or.inl (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 2 100 101 0 0 1 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase01
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase02
def t : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
def s : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))
def tx : Tree := (.leaf 2)
def sx : Tree := (.leaf 2)
def ty : Tree := (.node (.leaf 0) (.leaf 1))
def sy : Tree := (.node (.leaf 0) (.leaf 1))
def mxt : Tree := (.node (.leaf 100) (.leaf 2))
def mxs : Tree := (.node (.leaf 100) (.leaf 2))
def myt : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 101))
def mys : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 101)))
def xs : List Nat := [2]
def ys : List Nat := [0,1]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 0) (.leaf 1)),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[true,true],(.leaf 2),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 1 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    2 0 100 101 0 0 0 1
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase02
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase03
def t : Tree := (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 2) (.leaf 3))))
def s : Tree := (.node (.leaf 2) (.node (.leaf 3) (.node (.leaf 0) (.leaf 1))))
def tx : Tree := (.node (.leaf 0) (.leaf 1))
def sx : Tree := (.node (.leaf 0) (.leaf 1))
def ty : Tree := (.node (.leaf 2) (.leaf 3))
def sy : Tree := (.node (.leaf 2) (.leaf 3))
def mxt : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 100)))
def mxs : Tree := (.node (.leaf 100) (.node (.leaf 0) (.leaf 1)))
def myt : Tree := (.node (.leaf 101) (.node (.leaf 2) (.leaf 3)))
def mys : Tree := (.node (.leaf 2) (.node (.leaf 3) (.leaf 101)))
def xs : List Nat := [0,1]
def ys : List Nat := [2,3]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[true,true],(.node (.leaf 2) (.leaf 3)),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[true,true],(.node (.leaf 0) (.leaf 1)),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 1 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 2 100 101 0 0 1 1
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase03
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase04
def t : Tree := (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3))
def s : Tree := (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.leaf 3))
def tx : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
def sx : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))
def ty : Tree := (.leaf 3)
def sy : Tree := (.leaf 3)
def mxt : Tree := (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 100))
def mxs : Tree := (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.leaf 100))
def myt : Tree := (.node (.leaf 101) (.leaf 3))
def mys : Tree := (.node (.leaf 101) (.leaf 3))
def xs : List Nat := [0,1,2]
def ys : List Nat := [3]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.node (.leaf 0) (.node (.leaf 1) (.leaf 2))),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 1 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 3 100 101 1 0 1 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase04
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase05
def t : Tree := (.node (.leaf 8) (.leaf 10000))
def s : Tree := (.node (.leaf 8) (.leaf 10000))
def tx : Tree := (.leaf 8)
def sx : Tree := (.leaf 8)
def ty : Tree := (.leaf 10000)
def sy : Tree := (.leaf 10000)
def mxt : Tree := (.node (.leaf 8) (.leaf 1000003))
def mxs : Tree := (.node (.leaf 8) (.leaf 1000003))
def myt : Tree := (.node (.leaf 1000033) (.leaf 10000))
def mys : Tree := (.node (.leaf 1000033) (.leaf 10000))
def xs : List Nat := [8]
def ys : List Nat := [10000]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.leaf 8),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.leaf 8),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 0 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    8 10000 1000003 1000033 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase05
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase06
def t : Tree := (.node (.node (.leaf 3) (.leaf 2)) (.node (.leaf 1) (.leaf 0)))
def s : Tree := (.node (.node (.leaf 3) (.leaf 2)) (.node (.leaf 1) (.leaf 0)))
def tx : Tree := (.node (.leaf 1) (.leaf 0))
def sx : Tree := (.node (.leaf 1) (.leaf 0))
def ty : Tree := (.node (.leaf 3) (.leaf 2))
def sy : Tree := (.node (.leaf 3) (.leaf 2))
def mxt : Tree := (.node (.leaf 100) (.node (.leaf 1) (.leaf 0)))
def mxs : Tree := (.node (.leaf 100) (.node (.leaf 1) (.leaf 0)))
def myt : Tree := (.node (.node (.leaf 3) (.leaf 2)) (.leaf 101))
def mys : Tree := (.node (.node (.leaf 3) (.leaf 2)) (.leaf 101))
def xs : List Nat := [0,1]
def ys : List Nat := [2,3]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 3) (.leaf 2)),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.node (.leaf 3) (.leaf 2)),by decide,by decide,Or.inl (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 0 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 2 100 101 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase06
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase07
def t : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
def s : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
def tx : Tree := (.node (.leaf 0) (.leaf 1))
def sx : Tree := (.node (.leaf 0) (.leaf 1))
def ty : Tree := (.node (.leaf 2) (.leaf 3))
def sy : Tree := (.node (.leaf 2) (.leaf 3))
def mxt : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 100))
def mxs : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 100))
def myt : Tree := (.node (.leaf 101) (.node (.leaf 2) (.leaf 3)))
def mys : Tree := (.node (.leaf 101) (.node (.leaf 2) (.leaf 3)))
def xs : List Nat := [0,1]
def ys : List Nat := [2,3]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 0) (.leaf 1)),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.node (.leaf 0) (.leaf 1)),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 0 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 2 100 101 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase07
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase08
def t : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.node (.leaf 1009) (.leaf 10007)))
def s : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.node (.leaf 1009) (.leaf 10007)))
def tx : Tree := (.node (.leaf 17) (.leaf 103))
def sx : Tree := (.node (.leaf 17) (.leaf 103))
def ty : Tree := (.node (.leaf 1009) (.leaf 10007))
def sy : Tree := (.node (.leaf 1009) (.leaf 10007))
def mxt : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1000003))
def mxs : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1000003))
def myt : Tree := (.node (.leaf 1000033) (.node (.leaf 1009) (.leaf 10007)))
def mys : Tree := (.node (.leaf 1000033) (.node (.leaf 1009) (.leaf 10007)))
def xs : List Nat := [17,103]
def ys : List Nat := [1009,10007]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 17) (.leaf 103)),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.node (.leaf 17) (.leaf 103)),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 0 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    17 1009 1000003 1000033 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase08
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase09
def t : Tree := (.node (.leaf 2) (.node (.leaf 1) (.leaf 0)))
def s : Tree := (.node (.node (.leaf 2) (.leaf 1)) (.leaf 0))
def tx : Tree := (.node (.leaf 1) (.leaf 0))
def sx : Tree := (.node (.leaf 1) (.leaf 0))
def ty : Tree := (.leaf 2)
def sy : Tree := (.leaf 2)
def mxt : Tree := (.node (.leaf 100) (.node (.leaf 1) (.leaf 0)))
def mxs : Tree := (.node (.node (.leaf 100) (.leaf 1)) (.leaf 0))
def myt : Tree := (.node (.leaf 2) (.leaf 101))
def mys : Tree := (.node (.leaf 2) (.leaf 101))
def xs : List Nat := [0,1]
def ys : List Nat := [2]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.leaf 2),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false,false],(.leaf 2),by decide,by decide,Or.inl (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 2 100 101 0 0 1 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase09
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase10
def t : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))
def s : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
def tx : Tree := (.node (.leaf 0) (.leaf 1))
def sx : Tree := (.node (.leaf 0) (.leaf 1))
def ty : Tree := (.leaf 2)
def sy : Tree := (.leaf 2)
def mxt : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 100)))
def mxs : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 100))
def myt : Tree := (.node (.leaf 101) (.leaf 2))
def mys : Tree := (.node (.leaf 101) (.leaf 2))
def xs : List Nat := [0,1]
def ys : List Nat := [2]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[true,true],(.leaf 2),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.node (.leaf 0) (.leaf 1)),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 2 100 101 0 0 1 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase10
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase11
def t : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1009))
def s : Tree := (.node (.leaf 17) (.node (.leaf 103) (.leaf 1009)))
def tx : Tree := (.node (.leaf 17) (.leaf 103))
def sx : Tree := (.node (.leaf 17) (.leaf 103))
def ty : Tree := (.leaf 1009)
def sy : Tree := (.leaf 1009)
def mxt : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1000003))
def mxs : Tree := (.node (.leaf 17) (.node (.leaf 103) (.leaf 1000003)))
def myt : Tree := (.node (.leaf 1000033) (.leaf 1009))
def mys : Tree := (.node (.leaf 1000033) (.leaf 1009))
def xs : List Nat := [17,103]
def ys : List Nat := [1009]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 17) (.leaf 103)),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[true,true],(.leaf 1009),by decide,by decide,Or.inl (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    17 1009 1000003 1000033 0 0 1 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase11
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase12
def t : Tree := (.node (.leaf 2) (.node (.leaf 1) (.leaf 0)))
def s : Tree := (.node (.node (.leaf 2) (.leaf 1)) (.leaf 0))
def tx : Tree := (.leaf 2)
def sx : Tree := (.leaf 2)
def ty : Tree := (.node (.leaf 1) (.leaf 0))
def sy : Tree := (.node (.leaf 1) (.leaf 0))
def mxt : Tree := (.node (.leaf 2) (.leaf 100))
def mxs : Tree := (.node (.leaf 2) (.leaf 100))
def myt : Tree := (.node (.leaf 101) (.node (.leaf 1) (.leaf 0)))
def mys : Tree := (.node (.node (.leaf 101) (.leaf 1)) (.leaf 0))
def xs : List Nat := [2]
def ys : List Nat := [0,1]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.leaf 2),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false,false],(.leaf 2),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 1 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    2 0 100 101 0 0 0 1
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase12
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase13
def t : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))
def s : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
def tx : Tree := (.leaf 2)
def sx : Tree := (.leaf 2)
def ty : Tree := (.node (.leaf 0) (.leaf 1))
def sy : Tree := (.node (.leaf 0) (.leaf 1))
def mxt : Tree := (.node (.leaf 100) (.leaf 2))
def mxs : Tree := (.node (.leaf 100) (.leaf 2))
def myt : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 101)))
def mys : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 101))
def xs : List Nat := [2]
def ys : List Nat := [0,1]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[true,true],(.leaf 2),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.node (.leaf 0) (.leaf 1)),by decide,by decide,Or.inl (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 1 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    2 0 100 101 0 0 0 1
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase13
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase14
def t : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1009))
def s : Tree := (.node (.leaf 17) (.node (.leaf 103) (.leaf 1009)))
def tx : Tree := (.leaf 1009)
def sx : Tree := (.leaf 1009)
def ty : Tree := (.node (.leaf 17) (.leaf 103))
def sy : Tree := (.node (.leaf 17) (.leaf 103))
def mxt : Tree := (.node (.leaf 1000003) (.leaf 1009))
def mxs : Tree := (.node (.leaf 1000003) (.leaf 1009))
def myt : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1000033))
def mys : Tree := (.node (.leaf 17) (.node (.leaf 103) (.leaf 1000033)))
def xs : List Nat := [1009]
def ys : List Nat := [17,103]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 17) (.leaf 103)),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[true,true],(.leaf 1009),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 1 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    1009 17 1000003 1000033 0 0 0 1
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase14
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase15
def t : Tree := (.node (.node (.node (.leaf 3) (.leaf 2)) (.leaf 1)) (.leaf 0))
def s : Tree := (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 3)) (.leaf 2))
def tx : Tree := (.node (.leaf 1) (.leaf 0))
def sx : Tree := (.node (.leaf 1) (.leaf 0))
def ty : Tree := (.node (.leaf 3) (.leaf 2))
def sy : Tree := (.node (.leaf 3) (.leaf 2))
def mxt : Tree := (.node (.node (.leaf 100) (.leaf 1)) (.leaf 0))
def mxs : Tree := (.node (.node (.leaf 1) (.leaf 0)) (.leaf 100))
def myt : Tree := (.node (.node (.leaf 3) (.leaf 2)) (.leaf 101))
def mys : Tree := (.node (.node (.leaf 101) (.leaf 3)) (.leaf 2))
def xs : List Nat := [0,1]
def ys : List Nat := [2,3]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false,false],(.node (.leaf 3) (.leaf 2)),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false,false],(.node (.leaf 1) (.leaf 0)),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 1 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 2 100 101 0 0 1 1
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase15
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase16
def t : Tree := (.node (.leaf 2) (.node (.leaf 3) (.node (.leaf 0) (.leaf 1))))
def s : Tree := (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 2) (.leaf 3))))
def tx : Tree := (.node (.leaf 0) (.leaf 1))
def sx : Tree := (.node (.leaf 0) (.leaf 1))
def ty : Tree := (.node (.leaf 2) (.leaf 3))
def sy : Tree := (.node (.leaf 2) (.leaf 3))
def mxt : Tree := (.node (.leaf 100) (.node (.leaf 0) (.leaf 1)))
def mxs : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 100)))
def myt : Tree := (.node (.leaf 2) (.node (.leaf 3) (.leaf 101)))
def mys : Tree := (.node (.leaf 101) (.node (.leaf 2) (.leaf 3)))
def xs : List Nat := [0,1]
def ys : List Nat := [2,3]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[true,true],(.node (.leaf 0) (.leaf 1)),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[true,true],(.node (.leaf 2) (.leaf 3)),by decide,by decide,Or.inl (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 1 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 2 100 101 0 0 1 1
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase16
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase17
def t : Tree := (.node (.leaf 17) (.node (.leaf 103) (.node (.leaf 1009) (.leaf 10007))))
def s : Tree := (.node (.leaf 1009) (.node (.leaf 10007) (.node (.leaf 17) (.leaf 103))))
def tx : Tree := (.node (.leaf 17) (.leaf 103))
def sx : Tree := (.node (.leaf 17) (.leaf 103))
def ty : Tree := (.node (.leaf 1009) (.leaf 10007))
def sy : Tree := (.node (.leaf 1009) (.leaf 10007))
def mxt : Tree := (.node (.leaf 17) (.node (.leaf 103) (.leaf 1000003)))
def mxs : Tree := (.node (.leaf 1000003) (.node (.leaf 17) (.leaf 103)))
def myt : Tree := (.node (.leaf 1000033) (.node (.leaf 1009) (.leaf 10007)))
def mys : Tree := (.node (.leaf 1009) (.node (.leaf 10007) (.leaf 1000033)))
def xs : List Nat := [17,103]
def ys : List Nat := [1009,10007]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[true,true],(.node (.leaf 1009) (.leaf 10007)),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[true,true],(.node (.leaf 17) (.leaf 103)),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 1 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    17 1009 1000003 1000033 0 0 1 1
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase17
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase18
def t : Tree := (.node (.leaf 3) (.node (.leaf 2) (.node (.leaf 1) (.leaf 0))))
def s : Tree := (.node (.leaf 3) (.node (.node (.leaf 2) (.leaf 1)) (.leaf 0)))
def tx : Tree := (.node (.leaf 2) (.node (.leaf 1) (.leaf 0)))
def sx : Tree := (.node (.node (.leaf 2) (.leaf 1)) (.leaf 0))
def ty : Tree := (.leaf 3)
def sy : Tree := (.leaf 3)
def mxt : Tree := (.node (.leaf 100) (.node (.leaf 2) (.node (.leaf 1) (.leaf 0))))
def mxs : Tree := (.node (.leaf 100) (.node (.node (.leaf 2) (.leaf 1)) (.leaf 0)))
def myt : Tree := (.node (.leaf 3) (.leaf 101))
def mys : Tree := (.node (.leaf 3) (.leaf 101))
def xs : List Nat := [0,1,2]
def ys : List Nat := [3]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.leaf 3),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.leaf 3),by decide,by decide,Or.inl (by decide)⟩
theorem local0 : IsMinimum tx sx 1 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 3 100 101 1 0 1 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase18
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase19
def t : Tree := (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.leaf 3))
def s : Tree := (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3))
def tx : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))
def sx : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
def ty : Tree := (.leaf 3)
def sy : Tree := (.leaf 3)
def mxt : Tree := (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.leaf 100))
def mxs : Tree := (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 100))
def myt : Tree := (.node (.leaf 101) (.leaf 3))
def mys : Tree := (.node (.leaf 101) (.leaf 3))
def xs : List Nat := [0,1,2]
def ys : List Nat := [3]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 0) (.node (.leaf 1) (.leaf 2))),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 1 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 3 100 101 1 0 1 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase19
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase20
def t : Tree := (.node (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1009)) (.leaf 10007))
def s : Tree := (.node (.node (.leaf 17) (.node (.leaf 103) (.leaf 1009))) (.leaf 10007))
def tx : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1009))
def sx : Tree := (.node (.leaf 17) (.node (.leaf 103) (.leaf 1009)))
def ty : Tree := (.leaf 10007)
def sy : Tree := (.leaf 10007)
def mxt : Tree := (.node (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1009)) (.leaf 1000003))
def mxs : Tree := (.node (.node (.leaf 17) (.node (.leaf 103) (.leaf 1009))) (.leaf 1000003))
def myt : Tree := (.node (.leaf 1000033) (.leaf 10007))
def mys : Tree := (.node (.leaf 1000033) (.leaf 10007))
def xs : List Nat := [17,103,1009]
def ys : List Nat := [10007]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.node (.leaf 17) (.leaf 103)) (.leaf 1009)),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.node (.leaf 17) (.node (.leaf 103) (.leaf 1009))),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 1 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    17 10007 1000003 1000033 1 0 1 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase20
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase21
def t : Tree := (.node (.leaf 10000) (.leaf 8))
def s : Tree := (.node (.leaf 10000) (.leaf 8))
def tx : Tree := (.leaf 8)
def sx : Tree := (.leaf 8)
def ty : Tree := (.leaf 10000)
def sy : Tree := (.leaf 10000)
def mxt : Tree := (.node (.leaf 1000003) (.leaf 8))
def mxs : Tree := (.node (.leaf 1000003) (.leaf 8))
def myt : Tree := (.node (.leaf 10000) (.leaf 1000033))
def mys : Tree := (.node (.leaf 10000) (.leaf 1000033))
def xs : List Nat := [8]
def ys : List Nat := [10000]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.leaf 10000),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.leaf 10000),by decide,by decide,Or.inl (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 0 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    8 10000 1000003 1000033 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase21
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase22
def t : Tree := (.node (.leaf 8) (.leaf 10000))
def s : Tree := (.node (.leaf 8) (.leaf 10000))
def tx : Tree := (.leaf 8)
def sx : Tree := (.leaf 8)
def ty : Tree := (.leaf 10000)
def sy : Tree := (.leaf 10000)
def mxt : Tree := (.node (.leaf 8) (.leaf 1000003))
def mxs : Tree := (.node (.leaf 8) (.leaf 1000003))
def myt : Tree := (.node (.leaf 1000033) (.leaf 10000))
def mys : Tree := (.node (.leaf 1000033) (.leaf 10000))
def xs : List Nat := [8]
def ys : List Nat := [10000]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.leaf 8),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.leaf 8),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 0 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    8 10000 1000003 1000033 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase22
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase23
def t : Tree := (.node (.leaf 99991) (.leaf 999983))
def s : Tree := (.node (.leaf 99991) (.leaf 999983))
def tx : Tree := (.leaf 99991)
def sx : Tree := (.leaf 99991)
def ty : Tree := (.leaf 999983)
def sy : Tree := (.leaf 999983)
def mxt : Tree := (.node (.leaf 99991) (.leaf 1000037))
def mxs : Tree := (.node (.leaf 99991) (.leaf 1000037))
def myt : Tree := (.node (.leaf 1000039) (.leaf 999983))
def mys : Tree := (.node (.leaf 1000039) (.leaf 999983))
def xs : List Nat := [99991]
def ys : List Nat := [999983]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.leaf 99991),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.leaf 99991),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 0 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    99991 999983 1000037 1000039 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
end OwnCase23
