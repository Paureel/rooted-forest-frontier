import SelectorGeometry
namespace Universal233.Rule5PaidSelector
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Rule5Local Rule5Classification Rule5FinalClassification Case322Extraction Case322PaidGuard
set_option maxRecDepth 24000

structure BottomData where
 w : RMAF.Vertex
 sa : Bool
 sc : Bool
 sb : Bool
 a : Nat
 b : Nat
 X : Tree
 deriving DecidableEq, Repr

def unorient (s : Bool) : Tree → Option (Tree × Tree)
 | .leaf _ => none
 | .node l r => some (if s then (r,l) else (l,r))

def parseBottom (S : Tree) (w : RMAF.Vertex) (sa sc sb : Bool) (a b c : Nat) : Option Tree := do
 let Z ← subtree S w
 let (V,B) ← unorient sb Z
 let (A,C) ← unorient sc V
 let (L,X) ← unorient sa A
 if B=.leaf b ∧ C=.leaf c ∧ L=.leaf a then some X else none

def rows (S : Tree) (a b c : Nat) : List BottomData :=
 (HardParent.vertices S).flatMap fun w => [false,true].flatMap fun sa =>
 [false,true].flatMap fun sc => [false,true].flatMap fun sb =>
 [(a,b),(b,a)].filterMap fun xy =>
 (parseBottom S w sa sc sb xy.1 xy.2 c).map (fun X => ⟨w,sa,sc,sb,xy.1,xy.2,X⟩)

instance leafAt_decidable (T : Tree) (q : RMAF.Vertex) (a : Nat) : Decidable (LeafAt T q a) := by
 unfold LeafAt; infer_instance

instance cherryAt_decidable (T : Tree) (q : RMAF.Vertex) (a b : Nat) : Decidable (CherryAt T q a b) := by
 unfold CherryAt; infer_instance

def leafAddress? (T : Tree) (a : Nat) : Option RMAF.Vertex :=
 (HardParent.vertices T).find? (fun q => decide (LeafAt T q a))

def LiteralProps (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 (R : BottomData) (C : Tree) (qa ub : RMAF.Vertex) : Prop :=
 properPair T S=true ∧
 subtree S R.w=some (bottom R.sa R.sc R.sb R.a R.b d.c R.X) ∧
 (∃ i∈HardParent.vertices T, CherryAt T i R.a R.b ∨ CherryAt T i R.b R.a) ∧
 (cuts S R.a R.b).length=2 ∧
 (∀ z∈leaves T, z∈leaves C ↔ z∉leaves R.X ∧ z≠d.c) ∧
 R.b∈leaves C ∧ d.c∉leaves C ∧
 LeafAt T qa R.a ∧ LeafAt T ub R.b ∧ LeafAt T u d.c ∧
 (incident T (leaves R.X)=[v,u] ∨ incident T (leaves R.X)=[u,v]) ∧
 v.dropLast∈minimalVertices (leaves R.X) T ∧ u.dropLast∈minimalVertices (leaves R.X) T ∧
 v∉minimalVertices (leaves R.X) T ∧ u∉minimalVertices (leaves R.X) T ∧
 subtreeLabels S d.badArc=leaves R.X ∧ EndpointOrder a b R.a R.b

instance (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 (R : BottomData) (C : Tree) (qa ub : RMAF.Vertex) : Decidable (LiteralProps T S a b d u v R C qa ub) := by
 unfold LiteralProps EndpointOrder
 infer_instance

def ofProps {T S : Tree} {a b : Nat} {d : BadSelection} {u v : RMAF.Vertex}
 {R : BottomData} {C : Tree} {qa ub : RMAF.Vertex}
 (core : subtree T v=some C) (h : LiteralProps T S a b d u v R C qa ub) : LiteralGeometry T S :=
 {X:=R.X,C:=C,w:=R.w,r:=v,qa:=qa,ub:=ub,uc:=u,sa:=R.sa,sc:=R.sc,sb:=R.sb,a:=R.a,b:=R.b,c:=d.c,
  properT:=(properPair_parts h.1).1,properS:=(properPair_parts h.1).2.1,same:=(properPair_parts h.1).2.2,
  source:=h.2.1,cherry:=by obtain ⟨i,_,hc⟩ := h.2.2.1; exact ⟨i,hc⟩,
  two:=h.2.2.2.1,core:=core,coreLabels:=h.2.2.2.2.1,bC:=h.2.2.2.2.2.1,
  cC:=h.2.2.2.2.2.2.1,leafA:=h.2.2.2.2.2.2.2.1,leafB:=h.2.2.2.2.2.2.2.2.1,
  leafC:=h.2.2.2.2.2.2.2.2.2.1,frontier:=h.2.2.2.2.2.2.2.2.2.2.1,
  tailR:=h.2.2.2.2.2.2.2.2.2.2.2.1,tailC:=h.2.2.2.2.2.2.2.2.2.2.2.2.1,
  offR:=h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,offC:=h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1}

def buildOne (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 (R : BottomData) : Option (LiteralGeometry T S) :=
 match hc : subtree T v, leafAddress? T R.a, leafAddress? T R.b with
 | some C,some qa,some ub =>
   if h : LiteralProps T S a b d u v R C qa ub then some (ofProps hc h) else none
 | _,_,_ => none

def buildForSecond (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex) :
 Option (LiteralGeometry T S) := (rows S a b d.c).findSome? (buildOne T S a b d u v)

structure SelectedPaid (T S : Tree) where
 d : BadSelection
 u : RMAF.Vertex
 v : RMAF.Vertex
 geometry : LiteralGeometry T S

def buildSelected (T S : Tree) (a b : Nat) : Option (SelectedPaid T S) :=
 match selectFinal T S a b with
 | some (.remaining d (.second u v)) =>
   (buildForSecond T S a b d u v).map (SelectedPaid.mk d u v)
 | _ => none

theorem parseBottom_complete {S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool} {a b c : Nat}
 (h : subtree S w=some (bottom sa sc sb a b c X)) : parseBottom S w sa sc sb a b c=some X := by
 rw [parseBottom,h]
 cases sa <;> cases sc <;> cases sb <;> simp [bottom,VC,AX,orient,unorient]

theorem row_mem {S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool} {a b x y c : Nat}
 (h : subtree S w=some (bottom sa sc sb x y c X)) (xy : EndpointOrder a b x y) :
 (⟨w,sa,sc,sb,x,y,X⟩ : BottomData)∈rows S a b c := by
 apply List.mem_flatMap.2
 refine ⟨w,(HardParent.vertices_correct S w).2 ⟨_,h⟩,?_⟩
 apply List.mem_flatMap.2
 refine ⟨sa,by cases sa <;> simp,?_⟩
 apply List.mem_flatMap.2
 refine ⟨sc,by cases sc <;> simp,?_⟩
 apply List.mem_flatMap.2
 refine ⟨sb,by cases sb <;> simp,List.mem_filterMap.2 ?_⟩
 refine ⟨(x,y),?_,?_⟩
 · rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp
 · simp [parseBottom_complete h]

theorem leafAddress_complete {T : Tree} {q : RMAF.Vertex} {a : Nat}
 (hn : (leaves T).Nodup) (hq : LeafAt T q a) : leafAddress? T a=some q := by
 unfold leafAddress?
 cases hf : (HardParent.vertices T).find? (fun p => decide (LeafAt T p a)) with
 | none =>
   have no := List.find?_eq_none.1 hf q ((HardParent.vertices_correct T q).2 hq.valid)
   exact False.elim (no (decide_eq_true hq))
 | some p =>
   have hp : LeafAt T p a := of_decide_eq_true (List.find?_some (p := fun q => decide (LeafAt T q a)) hf)
   have eq := leaf_unique hn hp hq
   subst p
   rfl

/-- Original literal guards are the only checks in the executable builder. -/
theorem props_of_literal {T S : Tree} {a b : Nat} {d : BadSelection} {u v : RMAF.Vertex}
 (D : LiteralGeometry T S) (r : D.r=v) (c : D.uc=u) (dc : D.c=d.c)
 (ql : subtreeLabels S d.badArc=leaves D.X) (xy : EndpointOrder a b D.a D.b) :
 LiteralProps T S a b d u v ⟨D.w,D.sa,D.sc,D.sb,D.a,D.b,D.X⟩ D.C D.qa D.ub := by
 have proper : properPair T S=true := by
   simp only [properPair,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.contains_iff_mem]
   exact ⟨⟨⟨D.properT,D.properS⟩,fun x hx => (D.same x).1 hx⟩,fun x hx => (D.same x).2 hx⟩
 have cherry : ∃ i∈HardParent.vertices T, CherryAt T i D.a D.b ∨ CherryAt T i D.b D.a := by
   obtain ⟨i,h|h⟩ := D.cherry
   · exact ⟨i,(HardParent.vertices_correct T i).2 ⟨_,h⟩,Or.inl h⟩
   · exact ⟨i,(HardParent.vertices_correct T i).2 ⟨_,h⟩,Or.inr h⟩
 dsimp only [LiteralProps]
 simpa only [←r,←c,←dc] using
   And.intro proper (And.intro D.source (And.intro cherry (And.intro D.two
   (And.intro D.coreLabels (And.intro D.bC (And.intro D.cC (And.intro D.leafA
   (And.intro D.leafB (And.intro D.leafC (And.intro D.frontier (And.intro D.tailR
   (And.intro D.tailC (And.intro D.offR (And.intro D.offC (And.intro ql xy)))))))))))))))

theorem buildOne_complete {T S : Tree} {a b : Nat} {d : BadSelection} {u v : RMAF.Vertex}
 (D : LiteralGeometry T S) (r : D.r=v) (c : D.uc=u) (dc : D.c=d.c)
 (ql : subtreeLabels S d.badArc=leaves D.X) (xy : EndpointOrder a b D.a D.b) :
 ∃ E, buildOne T S a b d u v ⟨D.w,D.sa,D.sc,D.sb,D.a,D.b,D.X⟩=some E := by
 have hc : subtree T v=some D.C := by rw [←r]; exact D.core
 have props := props_of_literal D r c dc ql xy
 unfold buildOne
 split
 · rename_i C qa ub hcore ha hb
   have eC : C=D.C := Option.some.inj (hcore.symm.trans hc)
   have ea : qa=D.qa := Option.some.inj (ha.symm.trans (leafAddress_complete D.properT D.leafA))
   have eb : ub=D.ub := Option.some.inj (hb.symm.trans (leafAddress_complete D.properT D.leafB))
   subst C; subst qa; subst ub
   exact ⟨_,dite_eq_left props⟩
 · rename_i hbad
   simp only [hc,leafAddress_complete D.properT D.leafA,leafAddress_complete D.properT D.leafB] at hbad
   exact False.elim (hbad D.C D.qa D.ub rfl rfl rfl)

theorem buildForSecond_complete {T S : Tree} {i u v : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : selectFinal T S a b=some (.remaining d (.second u v))) :
 ∃ D, buildForSecond T S a b d u v=some D := by
 obtain ⟨D,r,c,dc,ql,xy⟩ := selected_literal_exists ch ad sel
 have hm : (⟨D.w,D.sa,D.sc,D.sb,D.a,D.b,D.X⟩ : BottomData)∈rows S a b d.c :=
   row_mem (by rw [←dc]; exact D.source) xy
 obtain ⟨E,he⟩ := buildOne_complete D r c dc ql xy
 cases hb : buildForSecond T S a b d u v with
 | some F => exact ⟨F,rfl⟩
 | none =>
   have no := List.findSome?_eq_none_iff.1 hb _ hm
   rw [he] at no
   contradiction

theorem buildSelected_complete {T S : Tree} {i u v : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : selectFinal T S a b=some (.remaining d (.second u v))) :
 ∃ R, buildSelected T S a b=some R ∧ R.d=d ∧ R.u=u ∧ R.v=v := by
 obtain ⟨D,hd⟩ := buildForSecond_complete ch ad sel
 exact ⟨⟨d,u,v,D⟩,by simp [buildSelected,sel,hd],rfl,rfl,rfl⟩

end Universal233.Rule5PaidSelector
