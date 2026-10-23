import SelectedConsumers
namespace Universal233.Rule5SourceOrientation
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification Rule5FinalClassification

theorem first_subbranches {T S : Tree} {i u w : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (hz : selectFinal T S a b=some (.remaining d (.first u w))) {c : Child}
 (hc : c∈firstChildren S a b d) : c∈branches S a b := by
 have sound := final_selected_sound ch ad hz
 obtain ⟨v,s,t,X,x,y,xy,sib,base,cut,ql,rl⟩ := selected_base ch sound.1 sound.2.1
 have cs : c=singletonChild S x ∨ c=pendantChild S a b := by simpa [firstChildren,sib] using hc
 rcases cs with rfl|rfl
 · rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [branches]
 · simp [branches]

theorem third_subbranches {T S : Tree} {i u w : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (hz : selectFinal T S a b=some (.remaining d (.third u w))) {c : Child}
 (hc : c∈thirdChildren S a b d) : c∈branches S a b := by
 have sound := final_selected_sound ch ad hz
 obtain ⟨v,s,t,X,x,y,xy,sib,base,cut,ql,rl⟩ := selected_base ch sound.1 sound.2.1
 have cs : c=singletonChild S (otherEndpoint a b x) ∨ c=pendantChild S a b := by simpa [thirdChildren,sib] using hc
 rcases cs with rfl|rfl
 · by_cases h : x=a <;> simp [otherEndpoint,h,branches]
 · simp [branches]

theorem exact_cover_solver {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {children : List Child}
 (ch : CherryAt T i a b) (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (sub : ∀c,c∈children → c∈branches S a b)
 (cover : ∀F,agreement T S F=true → ∃c,c∈children ∧ ∃G,feasible T S c G ∧ G.length≤F.length)
 (solver : Child → Nat → Option (List (List Nat)))
 (ih : ∀c,c∈children → ExactBoundedChild T S solver c) (k : Nat) :
 OriginalWithin T S k ↔ ∃c,c∈children ∧ ∃G,childCall solver k c=some G := by
 constructor
 · rintro ⟨F,hF,hk⟩
   obtain ⟨c,hc,G,hG,len⟩ := cover F hF
   obtain ⟨hp,he,paid⟩ := branch_checks hnT hnS same ch (sub c hc)
   have rem := (remaining_correct k hp he paid).1 ⟨G,hG,by omega⟩
   exact ⟨c,hc,(child_call_success (ih c hc) k).2 rem⟩
 · rintro ⟨c,hc,out⟩
   have rem := (child_call_success (ih c hc) k).1 out
   obtain ⟨hp,he,paid⟩ := branch_checks hnT hnS same ch (sub c hc)
   obtain ⟨F,hF,hk⟩ := (remaining_correct k hp he paid).2 rem
   exact ⟨F,hF.1,hk⟩

theorem first_child_solver {T S : Tree} {i u w : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (hz : selectFinal T S a b=some (.remaining d (.first u w)))
 (solver : Child → Nat → Option (List (List Nat)))
 (ih : ∀c,c∈firstChildren S a b d → ExactBoundedChild T S solver c) (k : Nat) :
 OriginalWithin T S k ↔ ∃c,c∈firstChildren S a b d ∧ ∃G,childCall solver k c=some G := by
 have prop := properPair_parts (admitted_parts ad).1
 exact exact_cover_solver ch prop.1 prop.2.1 prop.2.2
   (fun _ hc => first_subbranches ch ad hz hc) (fun _ hF => selected_first_cover ch ad hz hF) solver ih k

theorem third_child_solver {T S : Tree} {i u w : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (hz : selectFinal T S a b=some (.remaining d (.third u w)))
 (solver : Child → Nat → Option (List (List Nat)))
 (ih : ∀c,c∈thirdChildren S a b d → ExactBoundedChild T S solver c) (k : Nat) :
 OriginalWithin T S k ↔ ∃c,c∈thirdChildren S a b d ∧ ∃G,childCall solver k c=some G := by
 have prop := properPair_parts (admitted_parts ad).1
 exact exact_cover_solver ch prop.1 prop.2.1 prop.2.2
   (fun _ hc => third_subbranches ch ad hz hc) (fun _ hF => selected_third_cover ch ad hz hF) solver ih k

/-- Literal child materialization and costs. The original source forest is
computed from each permanent partition; endpoint and pendant costs remain1,2. -/
theorem selected_child_states {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b=some .remaining) (hd : selectBad T S a b=some d) :
 (firstChildren S a b d).map Child.paid=[1,2] ∧ (thirdChildren S a b d).map Child.paid=[1,2] ∧
 ∀c,c∈firstChildren S a b d ∨ c∈thirdChildren S a b d →
 c.sourceForest=c.partition.filterMap (fun B => restrict B S) := by
 obtain ⟨v,s,t,X,x,y,xy,sib,base,cut,ql,rl⟩ := selected_base ch sel hd
 have len := (admitted_parts (selectLocal_cases sel).1).2.2.2.2
 have paid : (pendantChild S a b).paid=2 := by rw [(pendant_paid S a b).1]; exact len
 refine ⟨by simp [firstChildren,sib,paid,singletonChild,makeChild],by simp [thirdChildren,sib,paid,singletonChild,makeChild],?_⟩
 intro c hc
 have cs : c=singletonChild S x ∨ c=singletonChild S (otherEndpoint a b x) ∨ c=pendantChild S a b := by
   rcases hc with h|h
   · have hh : c=singletonChild S x ∨ c=pendantChild S a b := by simpa [firstChildren,sib] using h
     exact hh.elim Or.inl (fun e => Or.inr (Or.inr e))
   · have hh : c=singletonChild S (otherEndpoint a b x) ∨ c=pendantChild S a b := by simpa [thirdChildren,sib] using h
     exact Or.inr hh
 rcases cs with rfl|rfl|rfl <;> rfl

theorem selected_original_endpoint_cuts {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b=some .remaining) (hd : selectBad T S a b=some d) :
 ∃x y qx qy bx byy, ((x=a ∧ y=b) ∨ (x=b ∧ y=a)) ∧ siblingEndpoint? S d.badArc=some x ∧
 endpointBranch S x=some bx ∧ endpointBranch S y=some byy ∧
 bx.originalCuts=[qx] ∧ byy.originalCuts=[qy] ∧
 bx.child=singletonChild S x ∧ byy.child=singletonChild S y ∧
 bx.child.paid=bx.originalCuts.length ∧ byy.child.paid=byy.originalCuts.length ∧
 LeafAt S qx x ∧ qx≠[] ∧ LeafAt S qy y ∧ qy≠[] ∧
 (highBranch S a b).originalCuts=cuts S a b ∧ (highBranch S a b).child.paid=2 := by
 obtain ⟨v,s,t,X,x,y,xy,sib,base,cut,ql,rl⟩ := selected_base ch sel hd
 have prop := properPair_parts (admitted_parts (selectLocal_cases sel).1).1
 have aS := (prop.2.2 a).1 (leafAt_label T _ a (cherry_left ch))
 have bS := (prop.2.2 b).1 (leafAt_label T _ b (cherry_right ch))
 have xS : x∈leaves S := by rcases xy with ⟨hx,hy⟩|⟨hx,hy⟩; rw [hx]; exact aS; rw [hx]; exact bS
 have yS : y∈leaves S := by rcases xy with ⟨hx,hy⟩|⟨hx,hy⟩; rw [hy]; exact bS; rw [hy]; exact aS
 have ne : x≠y := by have ab := cherry_distinct prop.1 ch; rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩; exact ab; exact ab.symm
 obtain ⟨qx,bx,ex,cx,bcx,px,lx,nx⟩ := endpoint_literal xS yS ne
 obtain ⟨qy,byy,ey,cy,bcy,py,ly,ny⟩ := endpoint_literal yS xS ne.symm
 refine ⟨x,y,qx,qy,bx,byy,xy,sib,ex,ey,cx,cy,bcx,bcy,px,py,lx,nx,ly,ny,rfl,?_⟩
 exact (admitted_parts (selectLocal_cases sel).1).2.2.2.2
end Universal233.Rule5SourceOrientation
