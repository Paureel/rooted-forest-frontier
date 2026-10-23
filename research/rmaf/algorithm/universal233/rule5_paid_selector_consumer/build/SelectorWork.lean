import PaidRequests
namespace Universal233.Rule5PaidSelector
open RMAF HardParent

theorem flatMap_bound {α β : Type} (L : List α) (f : α → List β) (n : Nat)
 (h : ∀ a∈L,(f a).length≤n) : (L.flatMap f).length≤n*L.length := by
 induction L with
 | nil => simp
 | cons a L ih =>
   have ha := h a (by simp)
   have ht := ih (fun b hb => h b (by simp [hb]))
   simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
   omega

/-- At most sixteen checked literal bottom rows per original source vertex:
eight sibling patterns times two endpoint orders. -/
theorem rows_linear_bound (S : Tree) (a b c : Nat) :
 (rows S a b c).length≤16*(HardParent.vertices S).length := by
 apply flatMap_bound
 intro w hw
 have hb (sa sc sb : Bool) :
   ([(a,b),(b,a)].filterMap (fun xy =>
    (parseBottom S w sa sc sb xy.1 xy.2 c).map (fun X => (⟨w,sa,sc,sb,xy.1,xy.2,X⟩ : BottomData)))).length≤2 :=
   List.length_filterMap_le _ _
 have h0 := hb false false false
 have h1 := hb false false true
 have h2 := hb false true false
 have h3 := hb false true true
 have h4 := hb true false false
 have h5 := hb true false true
 have h6 := hb true true false
 have h7 := hb true true true
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]
 omega
end Universal233.Rule5PaidSelector
