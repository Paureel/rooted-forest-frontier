import AdmittedTerminalGeometry
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CoreGraph Universal233.HardParent

def ExitLeaf (S : Tree) (M : List Vertex) (y : Nat) : Prop :=
 ∃v,v∈Universal233.HardParent.vertices S ∧ v≠[] ∧ v.dropLast∈M ∧ v∉M ∧
  subtree S v=some (.leaf y)

def EndpointTerminal (selected : List Nat) (S : Tree) (M : List Vertex) : Prop :=
 ∃x y,HasCherry x y S ∧ selected.contains x=true ∧
  (selected.contains y=true ∨ ExitLeaf S M y)

theorem exitLeaf_left (l r : Tree) (root : Bool) (A B : List Vertex) (y : Nat)
 (exit : ExitLeaf l A y) : ExitLeaf (.node l r) (vertexFrame root A B) y := by
 obtain ⟨v,member,nonempty,parent,outside,leaf⟩:=exit
 have drop:(false::v).dropLast=false::v.dropLast := by
  cases v with | nil => contradiction | cons x xs => rfl
 refine ⟨false::v,?_,(by intro h;cases h),?_,?_,leaf⟩
 · simp [Universal233.HardParent.vertices,prependSide,member]
 · rw [drop];exact (frame_left_mem root A B v.dropLast).mpr parent
 · intro h;exact outside ((frame_left_mem root A B v).mp h)

theorem exitLeaf_right (l r : Tree) (root : Bool) (A B : List Vertex) (y : Nat)
 (exit : ExitLeaf r B y) : ExitLeaf (.node l r) (vertexFrame root A B) y := by
 obtain ⟨v,member,nonempty,parent,outside,leaf⟩:=exit
 have drop:(true::v).dropLast=true::v.dropLast := by
  cases v with | nil => contradiction | cons x xs => rfl
 refine ⟨true::v,?_,(by intro h;cases h),?_,?_,leaf⟩
 · simp [Universal233.HardParent.vertices,prependSide,member]
 · rw [drop];exact (frame_right_mem root A B v.dropLast).mpr parent
 · intro h;exact outside ((frame_right_mem root A B v).mp h)

theorem terminal_left (selected : List Nat) (l r : Tree) (root : Bool) (A B : List Vertex)
 (terminal:EndpointTerminal selected l A) : EndpointTerminal selected (.node l r) (vertexFrame root A B) := by
 obtain ⟨x,y,cherry,hit,partner⟩:=terminal
 refine ⟨x,y,.left cherry,hit,?_⟩
 rcases partner with good|exit
 · exact Or.inl good
 · exact Or.inr (exitLeaf_left l r root A B y exit)

theorem terminal_right (selected : List Nat) (l r : Tree) (root : Bool) (A B : List Vertex)
 (terminal:EndpointTerminal selected r B) : EndpointTerminal selected (.node l r) (vertexFrame root A B) := by
 obtain ⟨x,y,cherry,hit,partner⟩:=terminal
 refine ⟨x,y,.right cherry,hit,?_⟩
 rcases partner with good|exit
 · exact Or.inl good
 · exact Or.inr (exitLeaf_right l r root A B y exit)

theorem rooted_terminal_or_leaf (selected : List Nat) (S : Tree)
 (nonempty:rootedSpan selected S≠[])
 (boundary:LeafBoundary S (rootedSpan selected S)) :
 (∃x,S=.leaf x ∧ selected.contains x=true) ∨
 EndpointTerminal selected S (rootedSpan selected S) := by
 induction S with
 | leaf x =>
  cases hit:selected.contains x with
  | false =>
   apply False.elim;apply nonempty
   change (if selected.contains x then [[]] else [])=[]
   rw [hit];rfl
  | true => exact Or.inl ⟨x,rfl,hit⟩
 | node l r il ir =>
  have frame:rootedSpan selected (.node l r)=
   vertexFrame true (rootedSpan selected l) (rootedSpan selected r) := by
   have equation:rootedSpan selected (.node l r)=
    (if (rootedSpan selected l).isEmpty && (rootedSpan selected r).isEmpty then []
     else []::(prependSide false (rootedSpan selected l)++prependSide true (rootedSpan selected r))) := rfl
   by_cases both:((rootedSpan selected l).isEmpty && (rootedSpan selected r).isEmpty)=true
   · exact False.elim (nonempty (by rw [equation,if_pos both]))
   · rw [equation,if_neg both];rfl
  rw [frame] at boundary ⊢
  have bl:=leafBoundary_left l r true _ _ boundary
  have br:=leafBoundary_right l r true _ _ boundary
  by_cases left:rootedSpan selected l=[]
  · have right:rootedSpan selected r≠[] := by
     intro empty;apply nonempty;simp [rootedSpan,left,empty]
    have lb:LeafBoundary (.node l r) (vertexFrame true [] (rootedSpan selected r)) := by
     simpa only [left] using boundary
    obtain ⟨x,lLeaf⟩:=leafBoundary_empty_left l r _ lb
    rcases ir right br with ⟨y,rLeaf,hit⟩|terminal
    · right
      refine ⟨y,x,by rw [lLeaf,rLeaf];exact .swap,hit,Or.inr ?_⟩
      refine ⟨[false],?_,(by intro h;cases h),?_,?_,?_⟩
      · rw [lLeaf];simp [Universal233.HardParent.vertices,prependSide]
      · exact List.mem_cons_self
      · rw [frame_left_mem,left];simp
      · change some l=some (.leaf x);rw [lLeaf]
    · exact Or.inr (terminal_right selected l r true _ _ terminal)
  · rcases il left bl with ⟨x,lLeaf,hit⟩|terminal
    · by_cases right:rootedSpan selected r=[]
      · have rb:LeafBoundary (.node l r) (vertexFrame true (rootedSpan selected l) []) := by
         simpa only [right] using boundary
        obtain ⟨y,rLeaf⟩:=leafBoundary_empty_right l r _ rb
        right
        refine ⟨x,y,by rw [lLeaf,rLeaf];exact .here,hit,Or.inr ?_⟩
        refine ⟨[true],?_,(by intro h;cases h),?_,?_,?_⟩
        · rw [rLeaf];simp [Universal233.HardParent.vertices,prependSide]
        · exact List.mem_cons_self
        · rw [frame_right_mem,right];simp
        · change some r=some (.leaf y);rw [rLeaf]
      · rcases ir right br with ⟨y,rLeaf,hitR⟩|terminal
        · exact Or.inr ⟨x,y,by rw [lLeaf,rLeaf];exact .here,hit,Or.inl hitR⟩
        · exact Or.inr (terminal_right selected l r true _ _ terminal)
    · exact Or.inr (terminal_left selected l r true _ _ terminal)

theorem minimal_two_terminal (selected : List Nat) (S : Tree)
 (count:2≤((leaves S).filter selected.contains).length)
 (boundary:LeafBoundary S (minimalVertices selected S)) :
 EndpointTerminal selected S (minimalVertices selected S) := by
 induction S with
 | leaf x =>
  simp only [leaves,List.filter_cons,List.filter_nil] at count
  split at count <;> simp_all only [List.length_nil,List.length_cons] <;> omega
 | node l r il ir =>
  cases left:(rootedSpan selected l).isEmpty with
  | true =>
   have zero:=rooted_empty_selected_count_zero selected l left
   have cr:2≤((leaves r).filter selected.contains).length := by
    simpa only [leaves,List.filter_append,List.length_append,zero,Nat.zero_add] using count
   have frame:minimalVertices selected (.node l r)=vertexFrame false [] (minimalVertices selected r) := by
    simp only [minimalVertices,left,ite_true,vertexFrame,Bool.false_eq_true,ite_false,prependSide,List.map_nil,List.nil_append]
   rw [frame] at boundary ⊢
   exact terminal_right selected l r false [] _ (ir cr (leafBoundary_right l r false [] _ boundary))
  | false =>
   cases right:(rootedSpan selected r).isEmpty with
   | true =>
    have zero:=rooted_empty_selected_count_zero selected r right
    have cl:2≤((leaves l).filter selected.contains).length := by
     simpa only [leaves,List.filter_append,List.length_append,zero,Nat.add_zero] using count
    have frame:minimalVertices selected (.node l r)=vertexFrame false (minimalVertices selected l) [] := by
     simp only [minimalVertices,left,right,Bool.false_eq_true,ite_false,ite_true,vertexFrame,prependSide,List.map_nil,List.nil_append,List.append_nil]
    rw [frame] at boundary ⊢
    exact terminal_left selected l r false _ [] (il cl (leafBoundary_left l r false _ [] boundary))
   | false =>
    have frame:minimalVertices selected (.node l r)=vertexFrame true (rootedSpan selected l) (rootedSpan selected r) := by
     simp only [minimalVertices,left,right,Bool.false_eq_true,ite_false,vertexFrame,ite_true,List.singleton_append]
    rw [frame] at boundary ⊢
    have nl:rootedSpan selected l≠[] := by intro e;rw [e] at left;cases left
    have nr:rootedSpan selected r≠[] := by intro e;rw [e] at right;cases right
    rcases rooted_terminal_or_leaf selected l nl (leafBoundary_left l r true _ _ boundary) with ⟨x,lLeaf,hit⟩|terminal
    · rcases rooted_terminal_or_leaf selected r nr (leafBoundary_right l r true _ _ boundary) with ⟨y,rLeaf,hitR⟩|terminal
      · exact ⟨x,y,by rw [lLeaf,rLeaf];exact .here,hit,Or.inl hitR⟩
      · exact terminal_right selected l r true _ _ terminal
    · exact terminal_left selected l r true _ _ terminal

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.exitLeaf_left
#print axioms AdmittedRule5Author.exitLeaf_left
#check @AdmittedRule5Author.exitLeaf_right
#print axioms AdmittedRule5Author.exitLeaf_right
#check @AdmittedRule5Author.terminal_left
#print axioms AdmittedRule5Author.terminal_left
#check @AdmittedRule5Author.terminal_right
#print axioms AdmittedRule5Author.terminal_right
#check @AdmittedRule5Author.rooted_terminal_or_leaf
#print axioms AdmittedRule5Author.rooted_terminal_or_leaf
#check @AdmittedRule5Author.minimal_two_terminal
#print axioms AdmittedRule5Author.minimal_two_terminal
