import PaidSelectedBinding
namespace Universal233.Rule5RemainingLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork Rule5PaidSelector Rule5Classification Rule5FinalClassification Case322PaidGuard Case322Extraction

theorem unorient_payload (s : Bool) (Z V B : Tree) (h : unorient s Z=some (V,B)) :
 (leaves V).length+(leaves B).length=(leaves Z).length ∧ leaves V⊆leaves Z ∧ leaves B⊆leaves Z := by
 cases Z with
 | leaf x=>simp [unorient] at h
 | node l r=>
  cases s <;> simp only [unorient,Bool.false_eq_true,ite_false,ite_true] at h
  all_goals cases Option.some.inj h
  all_goals simp only [leaves,List.length_append]
  all_goals exact ⟨by omega,by intro x hx;simp [hx],by intro x hx;simp [hx]⟩

theorem parse_bottom_payload (S : Tree) (w : RMAF.Vertex) (sa sc sb : Bool) (a b c : Nat)
 {X : Tree} (h : parseBottom S w sa sc sb a b c=some X) :
 (leaves X).length≤(leaves S).length ∧ leaves X⊆leaves S := by
 cases hz:subtree S w with
 | none=>simp [parseBottom,hz] at h
 | some Z=>
  cases hb:unorient sb Z with
  | none=>simp [parseBottom,hz,hb] at h
  | some pair=>
   obtain ⟨V,B⟩:=pair
   cases hc:unorient sc V with
   | none=>simp [parseBottom,hz,hb,hc] at h
   | some pair=>
    obtain ⟨A,C⟩:=pair
    cases ha:unorient sa A with
    | none=>simp [parseBottom,hz,hb,hc,ha] at h
    | some pair=>
     obtain ⟨L,X'⟩:=pair
     simp only [parseBottom,hz,hb,hc,ha,Option.bind_some] at h
     split at h
     · cases Option.some.inj h
       have bz:=unorient_payload sb Z V B hb
       have cv:=unorient_payload sc V A C hc
       have aa:=unorient_payload sa A L X' ha
       have zs:=DepthOne.subtree_leaves_sublist S Z w hz
       exact ⟨by have:=zs.length_le;omega,fun z hz=>zs.subset (bz.2.1 (cv.2.1 (aa.2.2 hz)))⟩
     · simp at h

theorem row_parse (S : Tree) (a b c : Nat) {R : BottomData} (h : R∈rows S a b c) :
 R.w∈vertices S ∧ parseBottom S R.w R.sa R.sc R.sb R.a R.b c=some R.X ∧ EndpointOrder a b R.a R.b := by
 unfold rows at h
 obtain ⟨w,hw,h⟩:=List.mem_flatMap.1 h
 obtain ⟨sa,_,h⟩:=List.mem_flatMap.1 h
 obtain ⟨sc,_,h⟩:=List.mem_flatMap.1 h
 obtain ⟨sb,_,h⟩:=List.mem_flatMap.1 h
 obtain ⟨xy,hxy,h⟩:=List.mem_filterMap.1 h
 obtain ⟨X,hp,heq⟩:=Option.map_eq_some_iff.1 h
 cases heq
 refine ⟨hw,hp,?_⟩
 have choices : xy=(a,b) ∨ xy=(b,a):=by simpa using hxy
 rcases choices with rfl|rfl
 · exact Or.inl ⟨rfl,rfl⟩
 · exact Or.inr ⟨rfl,rfl⟩

theorem row_payload (S : Tree) (a b c : Nat) {R : BottomData} (h : R∈rows S a b c) :
 R.w.length+1≤(leaves S).length ∧ (leaves R.X).length≤(leaves S).length ∧
 leaves R.X⊆leaves S ∧ EndpointOrder a b R.a R.b := by
 have parsed:=row_parse S a b c h
 have body:=parse_bottom_payload S R.w R.sa R.sc R.sb R.a R.b c parsed.2.1
 exact ⟨vertices_address S (by rw [vertices_value];exact parsed.1),body.1,body.2,parsed.2.2⟩

theorem literal_call_payload (T S : Tree) (a b : Nat) (d : BadSelection) (v : RMAF.Vertex)
 {j : LiteralCall} (domain : LiteralCallDomain T S a b d v j) :
 j.row.w.length+1≤(leaves S).length ∧ (leaves j.row.X).length≤(leaves S).length ∧ leaves j.row.X⊆leaves S ∧
 (leaves j.core).length≤(leaves T).length ∧ leaves j.core⊆leaves T ∧
 j.qa.length+1≤(leaves T).length ∧ j.ub.length+1≤(leaves T).length ∧
 LeafAt T j.qa j.row.a ∧ LeafAt T j.ub j.row.b := by
 have row:=row_payload S a b d.c domain.1
 have core:=DepthOne.subtree_leaves_sublist T j.core v domain.2.1
 have qa:=leaf_address_payload T j.row.a (by rw [leaf_address_value];exact domain.2.2.1)
 have ub:=leaf_address_payload T j.row.b (by rw [leaf_address_value];exact domain.2.2.2)
 exact ⟨row.1,row.2.1,row.2.2.1,core.length_le,core.subset,qa.2.1,ub.2.1,qa.2.2,ub.2.2⟩
end Universal233.Rule5RemainingLocalWork
