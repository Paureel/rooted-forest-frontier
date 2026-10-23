import IncidentClassification
namespace Universal233.Rule5FinalClassification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification

structure BadSelection where
 badArc : RMAF.Vertex
 singletonArc : RMAF.Vertex
 c : Nat
 deriving Repr, DecidableEq

def badAt (T S : Tree) (e f : RMAF.Vertex) : Option BadSelection :=
 if e ≠ f ∧ restrictionAgrees T S (subtreeLabels S e) = false then
   match subtree S f with
   | some (.leaf c) => some ⟨e,f,c⟩
   | _ => none
 else none
def badCandidates (T S : Tree) (a b : Nat) : List BadSelection :=
 (cuts S a b).flatMap fun e => (cuts S a b).filterMap (badAt T S e)
def selectBad (T S : Tree) (a b : Nat) : Option BadSelection := (badCandidates T S a b).head?

theorem badAt_sound {T S : Tree} {e f : RMAF.Vertex} {d : BadSelection}
 (h : badAt T S e f = some d) : d.badArc=e ∧ d.singletonArc=f ∧ e≠f ∧
 restrictionAgrees T S (subtreeLabels S e) = false ∧ subtree S f = some (.leaf d.c) := by
 unfold badAt at h
 split at h
 · rename_i guard
   cases hs : subtree S f with
   | none => simp [hs] at h
   | some U =>
     cases U with
     | leaf c => simp only [hs] at h; cases Option.some.inj h; exact ⟨rfl,rfl,guard.1,guard.2,rfl⟩
     | node l r => simp [hs] at h
 · contradiction

theorem selectBad_sound {T S : Tree} {a b : Nat} {d : BadSelection}
 (h : selectBad T S a b = some d) : d.badArc ∈ cuts S a b ∧ d.singletonArc ∈ cuts S a b ∧
 d.badArc ≠ d.singletonArc ∧ restrictionAgrees T S (subtreeLabels S d.badArc) = false ∧
 subtree S d.singletonArc = some (.leaf d.c) := by
 obtain ⟨tail,ht⟩ := List.head?_eq_some_iff.1 h
 have mem : d ∈ badCandidates T S a b := by rw [ht]; simp
 obtain ⟨e,em,hh⟩ := List.mem_flatMap.1 mem
 obtain ⟨f,fm,hf⟩ := List.mem_filterMap.1 hh
 obtain ⟨de,df,ne,bad,hc⟩ := badAt_sound hf
 subst e; subst f
 exact ⟨em,fm,ne,bad,hc⟩

theorem selectBad_complete {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b = some .remaining) :
 ∃ d, selectBad T S a b = some d := by
 obtain ⟨e,f,c,eq,bad,hc,cl,gc⟩ := remaining_source_status ch sel
 have em : e ∈ cuts S a b := by rcases eq with eq | eq <;> simp [eq]
 have fm : f ∈ cuts S a b := by rcases eq with eq | eq <;> simp [eq]
 have ne : e ≠ f := by
   have nd : (cuts S a b).Nodup := pendantOriginal_nodup S a b
   rcases eq with eq | eq
   · simpa [eq] using nd
   · have hh : f≠e := by simpa [eq] using nd
     exact hh.symm
 have mem : (⟨e,f,c⟩ : BadSelection) ∈ badCandidates T S a b := by
   apply List.mem_flatMap.2
   refine ⟨e,em,List.mem_filterMap.2 ⟨f,fm,?_⟩⟩
   simp [badAt,ne,bad,hc]
 cases hh : badCandidates T S a b with
 | nil => rw [hh] at mem; contradiction
 | cons d ds => exact ⟨d,by simp [selectBad,hh]⟩

theorem two_members_order {A : Type} {L : List A} {e f : A}
 (len : L.length=2) (em : e∈L) (fm : f∈L) (ne : e≠f) : L=[e,f] ∨ L=[f,e] := by
 obtain ⟨u,v,eq⟩ := list_two_named L len
 have ee : e=u ∨ e=v := by simpa [eq] using em
 have ff : f=u ∨ f=v := by simpa [eq] using fm
 rcases ee with rfl | rfl <;> rcases ff with rfl | rfl
 · contradiction
 · exact Or.inl eq
 · exact Or.inr eq
 · contradiction

theorem selected_bad_context {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b = some .remaining)
 (hd : selectBad T S a b = some d) :
 partitionCheck (leaves T) [subtreeLabels S d.badArc,[d.c],coreLabels S a b] = true ∧
 pairwiseEmbeddings T [subtreeLabels S d.badArc,[d.c],coreLabels S a b] = true := by
 have facts := selectLocal_cases sel
 have part := admitted_parts facts.1
 have ds := selectBad_sound hd
 have order := two_members_order part.2.2.2.2 ds.1 ds.2.1 ds.2.2.1
 have cl : subtreeLabels S d.singletonArc = [d.c] := source_subtree_labels ds.2.2.2.2
 have hp := (admitted_ordered_checks facts.1 ch).1
 have he := part.2.2.2.1
 rcases order with eq | eq
 · simpa [pendantPartition,eq,cl] using And.intro hp he
 · have hp0 : partitionCheck (leaves T) [[d.c],subtreeLabels S d.badArc,coreLabels S a b] = true := by
     simpa [pendantPartition,eq,cl] using hp
   have he0 : pairwiseEmbeddings T [[d.c],subtreeLabels S d.badArc,coreLabels S a b] = true := by
     simpa [pendantPartition,eq,cl] using he
   exact ⟨(partition_swap_first _ _ _ _).symm ▸ hp0,embeddings_swap_first T _ _ _ he0⟩

def outsideCheck (T : Tree) (X : List Nat) (q : RMAF.Vertex) (x : Nat) : Bool :=
 (subtreeLabels T q).contains x != paint T X q

theorem outsideCheck_correct (T : Tree) (X : List Nat) (q : RMAF.Vertex) (x : Nat) :
 outsideCheck T X q x = true ↔ OutsideLabel T X q x := by
 unfold outsideCheck OutsideLabel paint
 cases hd : (subtreeLabels T q).contains x <;> cases hp : (minimalVertices X T).contains q <;>
   simp_all

inductive BoundarySelection where
 | one (q : RMAF.Vertex)
 | first (cArc coreArc : RMAF.Vertex)
 | second (cArc coreArc : RMAF.Vertex)
 | third (cArc coreArc : RMAF.Vertex)
 deriving Repr, DecidableEq

def selectBoundary (T : Tree) (X : List Nat) (c : Nat) : Option BoundarySelection :=
 match incident T X with
 | [q] => some (.one q)
 | [q,r] =>
   let u := if outsideCheck T X q c then q else r
   let v := if outsideCheck T X q c then r else q
   if paint T X u then some (.third u v)
   else if paint T X v then some (.first u v) else some (.second u v)
 | _ => none

def BoundarySound (T : Tree) (X C : List Nat) (c : Nat) : BoundarySelection → Prop
 | .one q => incident T X = [q]
 | .first u v => (incident T X=[u,v] ∨ incident T X=[v,u]) ∧ OutRegion T X u [c] ∧ InRegion T X v C
 | .second u v => (incident T X=[u,v] ∨ incident T X=[v,u]) ∧ OutRegion T X u [c] ∧ OutRegion T X v C
 | .third u v => (incident T X=[u,v] ∨ incident T X=[v,u]) ∧ InRegion T X u [c] ∧ OutRegion T X v C

theorem boundary_selector_complete {T : Tree} {X C : List Nat} {c : Nat}
 (hn : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,[c],C] = true)
 (he : pairwiseEmbeddings T [X,[c],C] = true) :
 ∃ z, selectBoundary T X c = some z ∧ BoundarySound T X C c z := by
 rcases incident_one_or_two hn hp he with ⟨q,hq⟩ | ⟨q,r,hi⟩
 · exact ⟨.one q,by simp [selectBoundary,hq],hq⟩
 · obtain ⟨u,v,uv,uc,vc⟩ := two_boundary_roles hn hp he hi
   have cL : c ∈ leaves T := block_labels hp (B:=[c]) (by simp) (by simp)
   have ucTrue : outsideCheck T X u c = true := (outsideCheck_correct _ _ _ _).2 ((uc c cL).2 rfl)
   have nc : c ∉ C := by
     have part := (executable_pairwiseEmbeddings T [X,[c],C]).1 he
     have dj := (List.pairwise_cons.1 (List.pairwise_cons.1 part).2).1 C (by simp)
     intro hc
     obtain ⟨w,hw⟩ := leaf_exists cL
     exact dj w ⟨(minimalVertices_correct [c] T w).1 ((minimalVertices_terminal [c] T w c hw).2 (by simp)),
       (minimalVertices_correct C T w).1 ((minimalVertices_terminal C T w c hw).2 hc)⟩
   have vcFalse : outsideCheck T X v c = false := by
     cases hh : outsideCheck T X v c
     · rfl
     · exact False.elim (nc ((vc c cL).1 ((outsideCheck_correct _ _ _ _).1 hh)))
   have order : incident T X=[u,v] ∨ incident T X=[v,u] := by
     rcases uv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
     · exact Or.inl hi
     · exact Or.inr hi
   have comp : selectBoundary T X c =
    if paint T X u then some (.third u v)
    else if paint T X v then some (.first u v) else some (.second u v) := by
     rcases uv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [selectBoundary,hi,ucTrue,vcFalse]
   have um : u ∈ incident T X := by rcases order with eq | eq <;> simp [eq]
   have vm : v ∈ incident T X := by rcases order with eq | eq <;> simp [eq]
   have ne : u≠v := by
     have nd : (incident T X).Nodup := (vertices_nodup T).filter _
     rcases order with eq | eq
     · simpa [eq] using nd
     · have hn : v≠u := by simpa [eq] using nd
       exact hn.symm
   have outU (h : Outgoing T X u) : OutRegion T X u [c] := by
     refine ⟨h,?_⟩; intro x hx; simpa [OutsideLabel,h.1] using uc x hx
   have inU (h : Incoming T X u) : InRegion T X u [c] := by
     refine ⟨h,?_⟩; intro x hx; simpa [OutsideLabel,h.1] using uc x hx
   have outV (h : Outgoing T X v) : OutRegion T X v C := by
     refine ⟨h,?_⟩; intro x hx; simpa [OutsideLabel,h.1] using vc x hx
   have inV (h : Incoming T X v) : InRegion T X v C := by
     refine ⟨h,?_⟩; intro x hx; simpa [OutsideLabel,h.1] using vc x hx
   rcases boundary_directions um with ui | uo <;> rcases boundary_directions vm with vi | vo
   · exact False.elim (ne (incoming_unique um vm ui vi))
   · exact ⟨.third u v,by simp [comp,paint,ui.1],order,inU ui,outV vo⟩
   · exact ⟨.first u v,by simp [comp,paint,uo.1,vi.1],order,outU uo,inV vi⟩
   · exact ⟨.second u v,by simp [comp,paint,uo.1,vo.1],order,outU uo,outV vo⟩

inductive FinalSelection where
 | prefix (s : LocalSelection)
 | remaining (d : BadSelection) (z : BoundarySelection)
 deriving Repr, DecidableEq

def selectFinal (T S : Tree) (a b : Nat) : Option FinalSelection :=
 match selectLocal T S a b with
 | none => none
 | some .remaining => do
   let d ← selectBad T S a b
   let z ← selectBoundary T (subtreeLabels S d.badArc) d.c
   pure (.remaining d z)
 | some s => some (.prefix s)

/-- The finite remaining classifier never refuses on the actual admitted
remaining branch. Its output has literal source arcs and original target
boundary geometry. Local surgeries still require the source-spine bridge. -/
theorem remaining_classifier_complete {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b = some .remaining) :
 ∃ d z, selectFinal T S a b = some (.remaining d z) ∧
 selectBad T S a b = some d ∧
 BoundarySound T (subtreeLabels S d.badArc) (coreLabels S a b) d.c z := by
 obtain ⟨d,hd⟩ := selectBad_complete ch sel
 obtain ⟨hp,he⟩ := selected_bad_context ch sel hd
 have proper := properPair_parts (admitted_parts (selectLocal_cases sel).1).1
 obtain ⟨z,hz,hs⟩ := boundary_selector_complete proper.1 hp he
 exact ⟨d,z,by simp [selectFinal,sel,hd,hz],hd,hs⟩

end Universal233.Rule5FinalClassification
