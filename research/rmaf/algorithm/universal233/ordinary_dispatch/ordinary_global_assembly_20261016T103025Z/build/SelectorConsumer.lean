import SelectorBuilder
namespace Universal233.Rule5PaidSelector
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Rule5Case322 Rule5Local Rule5Classification Rule5FinalClassification Case322Extraction Case322PaidGuard
set_option maxRecDepth 24000

def Bound (S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 {T : Tree} (D : LiteralGeometry T S) : Prop :=
 D.r=v ∧ D.uc=u ∧ D.c=d.c ∧ subtreeLabels S d.badArc=leaves D.X ∧ EndpointOrder a b D.a D.b

theorem buildOne_binding {T S : Tree} {a b : Nat} {d : BadSelection} {u v : RMAF.Vertex}
 {R : BottomData} {D : LiteralGeometry T S} (h : buildOne T S a b d u v R=some D) :
 Bound S a b d u v D := by
 unfold buildOne at h
 split at h
 · rename_i C qa ub hc ha hb
   split at h
   · rename_i props
     have eq : ofProps hc props=D := Option.some.inj h
     subst D
     have copy := props
     rcases copy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,ql,xy⟩
     exact ⟨rfl,rfl,rfl,ql,xy⟩
   · contradiction
 · contradiction

theorem buildForSecond_binding {T S : Tree} {a b : Nat} {d : BadSelection} {u v : RMAF.Vertex}
 {D : LiteralGeometry T S} (h : buildForSecond T S a b d u v=some D) : Bound S a b d u v D := by
 obtain ⟨R,_,hr⟩ := List.exists_of_findSome?_eq_some h
 exact buildOne_binding hr

theorem buildSelected_binding {T S : Tree} {a b : Nat} {R : SelectedPaid T S}
 (h : buildSelected T S a b=some R) :
 selectFinal T S a b=some (.remaining R.d (.second R.u R.v)) ∧ Bound S a b R.d R.u R.v R.geometry := by
 unfold buildSelected at h
 split at h
 · rename_i d u v sel
   obtain ⟨D,hd,eq⟩ := Option.map_eq_some_iff.1 h
   subst R
   exact ⟨sel,buildForSecond_binding hd⟩
 · contradiction

/-- The returned actual paid list is complete for every original AF; all
geometry came through the executable selected second builder. -/
theorem selected_original_cover {T S : Tree} {a b : Nat} {R : SelectedPaid T S}
 (h : buildSelected T S a b=some R) {F : List (List Nat)} (ha : agreement T S F=true) :
 ∃ child, child∈guardedPlan R.geometry ∧ OriginalCover T S F child.partition :=
 guarded_original_cover R.geometry ha

theorem selected_affordable_cover {T S : Tree} {a b : Nat} {R : SelectedPaid T S}
 (h : buildSelected T S a b=some R) (q : Nat) {F : List (List Nat)}
 (ha : agreement T S F=true) (budget : F.length-1≤q) :
 ∃ child,child∈guardedPlan R.geometry ∧ paid child≤q ∧
 ∃ G,agreement T S G=true ∧ G.length≤F.length ∧ Refines G child.partition ∧
   G.length-child.partition.length≤q-paid child :=
 guarded_affordable_cover R.geometry q ha budget

theorem selected_actual_guards {T S : Tree} {a b : Nat} {R : SelectedPaid T S}
 (h : buildSelected T S a b=some R) :
 ∀ child,child∈guardedPlan R.geometry → currentGuard T S child=true := by
 intro child hc
 exact (List.mem_filter.1 hc).2

theorem selected_full_paid_decrease {T S : Tree} {a b : Nat} {R : SelectedPaid T S}
 (h : buildSelected T S a b=some R) {q n : Nat}
 (request : n∈callbackRequests q (guardedPlan R.geometry)) : n<q :=
 guarded_query_decrease R.geometry request

/-- Role transport retains the same physical cuts, partition and paid budget. -/
theorem selected_role_binding {T S : Tree} {a b : Nat} {R : SelectedPaid T S}
 (h : buildSelected T S a b=some R) (child : Branch) :
 (swapBranch child).originalCuts=child.originalCuts ∧ (swapBranch child).partition=child.partition ∧
 current S T (swapBranch child)=current T S child ∧
 currentGuard S T (swapBranch child)=currentGuard T S child ∧ paid (swapBranch child)=paid child :=
 operational_role_binding T S child

end Universal233.Rule5PaidSelector
