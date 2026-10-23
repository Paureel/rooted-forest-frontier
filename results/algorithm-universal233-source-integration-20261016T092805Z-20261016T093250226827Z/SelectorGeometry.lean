import PaidCaller
import FinalInterface

/-! Problem-specific binding of the actual final second selector output to
all completed paid-caller original literal geometry fields. -/
namespace Universal233.Rule5PaidSelector
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Rule5Local Rule5Classification Rule5FinalClassification Case322Extraction Case322PaidGuard
set_option maxRecDepth 24000

def EndpointOrder (a b x y : Nat) : Prop := (x=a ∧ y=b) ∨ (x=b ∧ y=a)

theorem endpoint_cherry {T : Tree} {i : RMAF.Vertex} {a b x y : Nat}
 (ch : CherryAt T i a b) (xy : EndpointOrder a b x y) : ActualCherry T x y := by
 rcases xy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
 · exact ⟨i,Or.inl ch⟩
 · exact ⟨i,Or.inr ch⟩

theorem outgoing_singleton_leaf {T : Tree} {X : List Nat} {u : RMAF.Vertex} {c : Nat}
 (hn : (leaves T).Nodup) (inc : u∈incident T X) (region : OutRegion T X u [c]) :
 LeafAt T u c := by
 obtain ⟨U,hU⟩ := ((incident_spec T X u).1 inc).1
 have nd := (subtreeLabels_sublist T u).nodup hn
 rw [source_subtree_labels hU] at nd
 have eq : U=.leaf c := proper_one_label_tree nd (by
   intro x hx
   have hu : x∈subtreeLabels T u := by rw [source_subtree_labels hU]; exact hx
   have hT := (subtreeLabels_sublist T u).subset hu
   simpa using (region.2 x hT).1 hu)
 simpa [LeafAt,eq] using hU

/-- All fields are derived from the actual printed selector guards. The
source geometry is obtained from final_selected_sound, never an input. -/
theorem selected_literal_exists {T S : Tree} {i u v : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : selectFinal T S a b=some (.remaining d (.second u v))) :
 ∃ D : LiteralGeometry T S, D.r=v ∧ D.uc=u ∧ D.c=d.c ∧
   subtreeLabels S d.badArc=leaves D.X ∧ EndpointOrder a b D.a D.b := by
 have sound := final_selected_sound ch ad sel
 have prop := properPair_parts (admitted_parts ad).1
 obtain ⟨h,p,s,t,r,X,x,y,xy,be,cut,hp,hh,ctx⟩ := sound.2.2.1
 have geometry : subtree S h=some (bottom s t r x y d.c X) := by
   simpa only [bottom,VC,AX,orient,fork] using hh
 have ql : subtreeLabels S d.badArc=leaves X := by
   rw [be]
   exact source_subtree_labels (by rw [subtree_append hp]; exact fork_second s _ _)
 have ds := selectBad_sound sound.2.1
 have cl : subtreeLabels S d.singletonArc=[d.c] := source_subtree_labels ds.2.2.2.2
 have bd := sound.2.2.2
 have ui : u∈incident T (subtreeLabels S d.badArc) := by rcases bd.1 with eq|eq <;> simp [eq]
 have vi : v∈incident T (subtreeLabels S d.badArc) := by rcases bd.1 with eq|eq <;> simp [eq]
 obtain ⟨C,hC⟩ := ((incident_spec T (subtreeLabels S d.badArc) v).1 vi).1
 have leafC := outgoing_singleton_leaf prop.1 ui bd.2.1
 have xS : x∈leaves S := leafAt_label S _ x (bottom_a_lookup geometry)
 have yS : y∈leaves S := leafAt_label S _ y (bottom_b_lookup geometry)
 obtain ⟨qa,leafA⟩ := leaf_exists ((prop.2.2 x).2 xS)
 obtain ⟨ub,leafB⟩ := leaf_exists ((prop.2.2 y).2 yS)
 have labelsCore (z : Nat) (zT : z∈leaves T) : z∈leaves C ↔ z∉leaves X ∧ z≠d.c := by
   have zS := (prop.2.2 z).1 zT
   have zC : z∈leaves C ↔ z∈coreLabels S a b := by
     rw [←source_subtree_labels hC]
     exact bd.2.2.2 z zT
   rw [zC]
   constructor
   · intro hc
     have no := (mem_core S a b z).1 hc |>.2
     refine ⟨?_,?_⟩
     · rw [←ql]; exact no _ ds.1
     · intro he; apply no _ ds.2.1; simp [cl,he]
   · rintro ⟨nx,nc⟩
     exact core_of_neither_pendant cut ds.2.2.2.2 zS (ql.symm ▸ nx) nc
 have yC : y∈leaves C := by
   rw [←source_subtree_labels hC]
   apply (bd.2.2.2 y ((prop.2.2 y).2 yS)).2
   apply endpoint_core
   · rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩; exact Or.inr rfl; exact Or.inl rfl
   · exact yS
 have cC : d.c∉leaves C := by
   intro hc
   have cT := (subtreeLabels_sublist T v).subset (by rw [source_subtree_labels hC]; exact hc)
   exact ((labelsCore d.c cT).1 hc).2 rfl
 have two : (cuts S x y).length=2 := by
   rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
   · exact (admitted_parts ad).2.2.2.2
   · rw [cuts_swap]; exact (admitted_parts ad).2.2.2.2
 let D : LiteralGeometry T S :=
   { X:=X,C:=C,w:=h,r:=v,qa:=qa,ub:=ub,uc:=u,sa:=s,sc:=t,sb:=r,a:=x,b:=y,c:=d.c,
     properT:=prop.1,properS:=prop.2.1,same:=prop.2.2,source:=geometry,
     cherry:=endpoint_cherry ch xy,two:=two,core:=hC,coreLabels:=labelsCore,bC:=yC,cC:=cC,
     leafA:=leafA,leafB:=leafB,leafC:=leafC,
     frontier:=by rw [←ql]; exact bd.1.symm,
     tailR:=by rw [←ql]; exact bd.2.2.1.2,
     tailC:=by rw [←ql]; exact bd.2.1.1.2,
     offR:=by rw [←ql]; exact bd.2.2.1.1,
     offC:=by rw [←ql]; exact bd.2.1.1.1 }
 exact ⟨D,rfl,rfl,rfl,ql,xy⟩

end Universal233.Rule5PaidSelector
