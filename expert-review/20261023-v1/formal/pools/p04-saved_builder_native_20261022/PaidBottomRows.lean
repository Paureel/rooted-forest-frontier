import PaidSourceFork
import SourceSpine
import SourceOrientation
namespace PaidBuilderAuthor
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification OrdinaryDispatch
open Universal233.Hard2Overlap AdmittedRule5Author
open Universal233.Case322Extraction Universal233.Rule5PaidSelector

theorem two_members_orders {α : Type} (L : List α) (e f : α)
 (len:L.length=2) (he:e∈L) (hf:f∈L) (neq:e≠f) : L=[e,f] ∨ L=[f,e] := by
 cases L with
 | nil => cases he
 | cons x tail =>
  cases tail with
  | nil => exact False.elim (neq ((List.mem_singleton.mp he).trans (List.mem_singleton.mp hf).symm))
  | cons y rest =>
   cases rest with
   | cons z zs => simp only [List.length_cons] at len;omega
   | nil =>
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he hf
    rcases he with rfl|rfl <;> rcases hf with rfl|rfl
    · exact False.elim (neq rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (neq rfl)

theorem actual_selected_mate_forbidden (T S : Tree) (c d : Candidate) (bad : BadSelection)
 (a b : Nat) (proper:DepthOne.proper T S=true) (early:FastOrdinary.early T S=.hard2 c d)
 (pick:selectBad T S c.a c.b=some bad)
 (order:a=c.a ∧ b=c.b ∨ a=c.b ∧ b=c.a) : ¬HasCherry b bad.c S := by
 intro cherry
 have front:=actual_front_checks T S c d proper early
 have priority:=actual_rule4_priority_closed T S c d proper early
 have original:=hasCherry_bool_prop T c.a c.b front.2.1
 have neq:=hasCherry_ne original priority.1
 have facts:=selectBad_sound T S c.a c.b bad pick
 have cutsOrder:=two_members_perm (cuts S c.a c.b) bad.singletonArc bad.badArc
  front.2.2.2.2.1 facts.2.1 facts.1 facts.2.2.1.symm
 have single:=source_labels_of_subtree S bad.singletonArc (.leaf bad.c) facts.2.2.2.2
 rcases order with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
 · have reverseOrder:(pendantOriginal S c.b c.a).Perm [bad.singletonArc,bad.badArc] := by
    rw [pendantOriginal_swap S c.b c.a];exact cutsOrder
   have guard:Rule4.LocalGuard T S ⟨c.b,c.a,bad.c,bad.singletonArc,bad.badArc⟩ :=
    ⟨Rule4.orderedCherries_complete (hasCherry_prop_swap original),Rule4.orderedCherries_complete cherry,
     Ne.symm neq,reverseOrder,single⟩
   obtain ⟨choice,picked⟩:=Rule4.select_complete priority _ guard
   rw [front.2.2.2.2.2.1] at picked;cases picked
 · have guard:Rule4.LocalGuard T S ⟨c.a,c.b,bad.c,bad.singletonArc,bad.badArc⟩ :=
    ⟨Rule4.orderedCherries_complete original,Rule4.orderedCherries_complete cherry,neq,cutsOrder,single⟩
   obtain ⟨choice,picked⟩:=Rule4.select_complete priority _ guard
   rw [front.2.2.2.2.2.1] at picked;cases picked

theorem actual_second_source_bottom (T S : Tree) (c d : Candidate) (bad : BadSelection) (u v : Vertex)
 (proper:DepthOne.proper T S=true) (early:FastOrdinary.early T S=.hard2 c d)
 (pick:selectFinal T S c.a c.b=some (.remaining bad (.second u v))) :
 ∃w sa sc sb a b U, EndpointOrder c.a c.b a b ∧
  subtree S bad.badArc=some U ∧ subtreeLabels S bad.badArc=leaves U ∧
  subtree S w=some (bottom sa sc sb a b bad.c U) := by
 have badPick:=(selectFinal_remaining_facts T S c.a c.b bad (.second u v) pick).2.1
 obtain ⟨U,p,sa,a,b,order,badLocation,badEq,parentLocation⟩:=
  actual_second_endpoint_fork T S c d bad u v proper early pick
 have front:=actual_front_checks T S c d proper early
 have priority:=actual_rule4_priority_closed T S c d proper early
 have original:=hasCherry_bool_prop T c.a c.b front.2.1
 have neq:=hasCherry_ne original priority.1
 have endpoints:=actual_source_endpoint_members T S c d proper early
 have members:a∈leaves S ∧ b∈leaves S ∧ a≠b := by
  rcases order with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨endpoints.1,endpoints.2,neq⟩
  · exact ⟨endpoints.2,endpoints.1,Ne.symm neq⟩
 have facts:=selectBad_sound T S c.a c.b bad badPick
 have labels:=source_labels_of_subtree S bad.badArc U badLocation
 have nU:b∉leaves U := by
  rw [←labels]
  rcases order with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact source_label_outside_pendant facts.1 (Or.inr rfl) endpoints.2
  · exact source_label_outside_pendant facts.1 (Or.inl rfl) endpoints.1
 have cutsOrder:=two_members_orders (cuts S c.a c.b) bad.badArc bad.singletonArc
  front.2.2.2.2.1 facts.1 facts.2.1 facts.2.2.1
 have orientedCuts:cuts S a b=[p++[!sa],bad.singletonArc] ∨
  cuts S a b=[bad.singletonArc,p++[!sa]] := by
  rw [←badEq]
  rcases order with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact cutsOrder
  · change pendantOriginal S c.b c.a=_ ∨ pendantOriginal S c.b c.a=_
    rw [pendantOriginal_swap S c.b c.a];exact cutsOrder
 have forkLocation:subtree S p=some (fork sa (.leaf a) U) := parentLocation
 obtain ⟨w,sc,sb,location⟩:=source_two_pendant_spine priority.2.1 members.1 members.2.1 members.2.2
  forkLocation nU orientedCuts facts.2.2.2.2
  (actual_selected_mate_forbidden T S c d bad a b proper early badPick order)
 exact ⟨w,sa,sc,sb,a,b,U,order,badLocation,labels,location⟩

theorem parse_bottom_location (S U : Tree) (w : Vertex) (sa sc sb : Bool) (a b c : Nat)
 (location:subtree S w=some (bottom sa sc sb a b c U)) :
 parseBottom S w sa sc sb a b c=some U := by
 unfold parseBottom
 rw [location]
 cases sa <;> cases sc <;> cases sb <;>
  change (if (.leaf b:Tree)=.leaf b ∧ (.leaf c:Tree)=.leaf c ∧ (.leaf a:Tree)=.leaf a
   then some U else none)=some U
 all_goals exact if_pos ⟨rfl,rfl,rfl⟩

theorem literal_bottom_row (S U : Tree) (w : Vertex) (sa sc sb : Bool) (ca cb a b c : Nat)
 (order:EndpointOrder ca cb a b)
 (location:subtree S w=some (bottom sa sc sb a b c U)) :
 (⟨w,sa,sc,sb,a,b,U⟩:BottomData)∈rows S ca cb c := by
 have wm:w∈Universal233.HardParent.vertices S := (vertices_correct S w).mpr ⟨_,location⟩
 have saMem:sa∈[false,true] := by cases sa <;> decide
 have scMem:sc∈[false,true] := by cases sc <;> decide
 have sbMem:sb∈[false,true] := by cases sb <;> decide
 have xy:(a,b)∈[(ca,cb),(cb,ca)] := by
  rcases order with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
 change _∈(Universal233.HardParent.vertices S).flatMap _
 refine List.mem_flatMap.mpr ⟨w,wm,List.mem_flatMap.mpr ⟨sa,saMem,
  List.mem_flatMap.mpr ⟨sc,scMem,List.mem_flatMap.mpr ⟨sb,sbMem,
  List.mem_filterMap.mpr ⟨(a,b),xy,?_⟩⟩⟩⟩⟩
 rw [parse_bottom_location S U w sa sc sb a b c location]
 rfl

theorem actual_second_bottom_row (T S : Tree) (c d : Candidate) (bad : BadSelection) (u v : Vertex)
 (proper:DepthOne.proper T S=true) (early:FastOrdinary.early T S=.hard2 c d)
 (pick:selectFinal T S c.a c.b=some (.remaining bad (.second u v))) :
 ∃R∈rows S c.a c.b bad.c, EndpointOrder c.a c.b R.a R.b ∧
  subtree S bad.badArc=some R.X ∧ subtreeLabels S bad.badArc=leaves R.X ∧
  subtree S R.w=some (bottom R.sa R.sc R.sb R.a R.b bad.c R.X) := by
 obtain ⟨w,sa,sc,sb,a,b,U,order,badLocation,labels,location⟩:=
  actual_second_source_bottom T S c d bad u v proper early pick
 exact ⟨⟨w,sa,sc,sb,a,b,U⟩,literal_bottom_row S U w sa sc sb c.a c.b a b bad.c order location,
  order,badLocation,labels,location⟩

end PaidBuilderAuthor

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @PaidBuilderAuthor.two_members_orders
#print axioms PaidBuilderAuthor.two_members_orders
#check @PaidBuilderAuthor.actual_selected_mate_forbidden
#print axioms PaidBuilderAuthor.actual_selected_mate_forbidden
#check @PaidBuilderAuthor.actual_second_source_bottom
#print axioms PaidBuilderAuthor.actual_second_source_bottom
#check @PaidBuilderAuthor.parse_bottom_location
#print axioms PaidBuilderAuthor.parse_bottom_location
#check @PaidBuilderAuthor.literal_bottom_row
#print axioms PaidBuilderAuthor.literal_bottom_row
#check @PaidBuilderAuthor.actual_second_bottom_row
#print axioms PaidBuilderAuthor.actual_second_bottom_row
