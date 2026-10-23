import AdmittedRemainingSource
namespace PaidBuilderAuthor
open RMAF Universal233 Universal233.CoreGraph Universal233.HardParent AdmittedRule5Author

def ExitArc (S : Tree) (M : List Vertex) (v : Vertex) : Prop :=
 v∈Universal233.HardParent.vertices S ∧ v≠[] ∧ v.dropLast∈M ∧ v∉M

def LeafOrTreeBoundary (S : Tree) (M : List Vertex) (U : Tree) : Prop :=
 ∀v,ExitArc S M v → (∃x,subtree S v=some (.leaf x)) ∨ subtree S v=some U

def endpointForkTree (side : Bool) (a : Nat) (U : Tree) : Tree :=
 if side then .node U (.leaf a) else .node (.leaf a) U

def EndpointFork (selected : List Nat) (S : Tree) (M : List Vertex) (U : Tree) : Prop :=
 ∃p side a,subtree S p=some (endpointForkTree side a U) ∧ selected.contains a=true ∧
 ExitArc S M (p++[!side])

theorem root_vertex_member (S : Tree) : []∈Universal233.HardParent.vertices S := by
 cases S <;> exact List.mem_cons_self

theorem vertices_left_member (l r : Tree) (v : Vertex)
 (member:v∈Universal233.HardParent.vertices l) : (false::v)∈Universal233.HardParent.vertices (.node l r) := by
 exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨v,member,rfl⟩))

theorem vertices_right_member (l r : Tree) (v : Vertex)
 (member:v∈Universal233.HardParent.vertices r) : (true::v)∈Universal233.HardParent.vertices (.node l r) := by
 exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨v,member,rfl⟩))

theorem exitArc_left (l r : Tree) (root : Bool) (A B : List Vertex) (v : Vertex)
 (exit:ExitArc l A v) : ExitArc (.node l r) (vertexFrame root A B) (false::v) := by
 obtain ⟨member,nonempty,parent,outside⟩:=exit
 have drop:(false::v).dropLast=false::v.dropLast := by
  cases v with | nil => contradiction | cons x xs => rfl
 refine ⟨vertices_left_member l r v member,(by intro h;cases h),?_,?_⟩
 · rw [drop];exact (frame_left_mem root A B v.dropLast).mpr parent
 · intro h;exact outside ((frame_left_mem root A B v).mp h)

theorem exitArc_right (l r : Tree) (root : Bool) (A B : List Vertex) (v : Vertex)
 (exit:ExitArc r B v) : ExitArc (.node l r) (vertexFrame root A B) (true::v) := by
 obtain ⟨member,nonempty,parent,outside⟩:=exit
 have drop:(true::v).dropLast=true::v.dropLast := by
  cases v with | nil => contradiction | cons x xs => rfl
 refine ⟨vertices_right_member l r v member,(by intro h;cases h),?_,?_⟩
 · rw [drop];exact (frame_right_mem root A B v.dropLast).mpr parent
 · intro h;exact outside ((frame_right_mem root A B v).mp h)

theorem treeBoundary_left (l r U : Tree) (root : Bool) (A B : List Vertex)
 (boundary:LeafOrTreeBoundary (.node l r) (vertexFrame root A B) U) : LeafOrTreeBoundary l A U := by
 intro v exit
 exact boundary (false::v) (exitArc_left l r root A B v exit)

theorem treeBoundary_right (l r U : Tree) (root : Bool) (A B : List Vertex)
 (boundary:LeafOrTreeBoundary (.node l r) (vertexFrame root A B) U) : LeafOrTreeBoundary r B U := by
 intro v exit
 exact boundary (true::v) (exitArc_right l r root A B v exit)

theorem exitArc_empty_left (l r : Tree) (B : List Vertex) :
 ExitArc (.node l r) (vertexFrame true [] B) [false] := by
 refine ⟨vertices_left_member l r [] (root_vertex_member l),(by intro h;cases h),List.mem_cons_self,?_⟩
 intro h
 exact List.not_mem_nil ((frame_left_mem true [] B []).mp h)

theorem exitArc_empty_right (l r : Tree) (A : List Vertex) :
 ExitArc (.node l r) (vertexFrame true A []) [true] := by
 refine ⟨vertices_right_member l r [] (root_vertex_member r),(by intro h;cases h),List.mem_cons_self,?_⟩
 intro h
 exact List.not_mem_nil ((frame_right_mem true A [] []).mp h)

theorem fork_left (selected : List Nat) (l r U : Tree) (root : Bool) (A B : List Vertex)
 (fork:EndpointFork selected l A U) : EndpointFork selected (.node l r) (vertexFrame root A B) U := by
 obtain ⟨p,side,x,location,hit,exit⟩:=fork
 exact ⟨false::p,side,x,location,hit,exitArc_left l r root A B (p++[!side]) exit⟩

theorem fork_right (selected : List Nat) (l r U : Tree) (root : Bool) (A B : List Vertex)
 (fork:EndpointFork selected r B U) : EndpointFork selected (.node l r) (vertexFrame root A B) U := by
 obtain ⟨p,side,x,location,hit,exit⟩:=fork
 exact ⟨true::p,side,x,location,hit,exitArc_right l r root A B (p++[!side]) exit⟩

theorem rooted_terminal_fork_or_leaf (selected : List Nat) (S U : Tree)
 (nonempty:rootedSpan selected S≠[])
 (boundary:LeafOrTreeBoundary S (rootedSpan selected S) U) :
 (∃x,S=.leaf x ∧ selected.contains x=true) ∨
 EndpointTerminal selected S (rootedSpan selected S) ∨ EndpointFork selected S (rootedSpan selected S) U := by
 induction S with
 | leaf x =>
  cases hit:selected.contains x with
  | false =>
   apply False.elim;apply nonempty
   change (if selected.contains x then [[]] else [])=[]
   rw [hit];rfl
  | true => exact Or.inl ⟨x,rfl,hit⟩
 | node l r il ir =>
  have frame:rootedSpan selected (.node l r)=vertexFrame true (rootedSpan selected l) (rootedSpan selected r) := by
   have equation:rootedSpan selected (.node l r)=
    (if (rootedSpan selected l).isEmpty && (rootedSpan selected r).isEmpty then []
     else []::(prependSide false (rootedSpan selected l)++prependSide true (rootedSpan selected r))) := rfl
   by_cases both:((rootedSpan selected l).isEmpty && (rootedSpan selected r).isEmpty)=true
   · exact False.elim (nonempty (by rw [equation,if_pos both]))
   · rw [equation,if_neg both];rfl
  rw [frame] at boundary ⊢
  have bl:=treeBoundary_left l r U true _ _ boundary
  have br:=treeBoundary_right l r U true _ _ boundary
  by_cases left:rootedSpan selected l=[]
  · have right:rootedSpan selected r≠[] := by
     intro empty;apply nonempty;simp only [rootedSpan,left,empty];rfl
    rcases ir right br with ⟨y,rLeaf,hit⟩|terminal|fork
    · have exit:ExitArc (.node l r) (vertexFrame true (rootedSpan selected l) (rootedSpan selected r)) [false] := by
       rw [left];exact exitArc_empty_left l r _
      rcases boundary [false] exit with ⟨x,loc⟩|loc
      · have lLeaf:l=.leaf x:=Option.some.inj loc
        right;left
        exact ⟨y,x,by rw [lLeaf,rLeaf];exact .swap,hit,Or.inr ⟨[false],exit.1,exit.2.1,exit.2.2.1,exit.2.2.2,loc⟩⟩
      · have lU:l=U:=Option.some.inj loc
        right;right
        refine ⟨[],true,y,?_,hit,exit⟩
        change some (.node l r)=some (endpointForkTree true y U)
        rw [lU,rLeaf];rfl
    · exact Or.inr (Or.inl (terminal_right selected l r true _ _ terminal))
    · exact Or.inr (Or.inr (fork_right selected l r U true _ _ fork))
  · rcases il left bl with ⟨x,lLeaf,hit⟩|terminal|fork
    · by_cases right:rootedSpan selected r=[]
      · have exit:ExitArc (.node l r) (vertexFrame true (rootedSpan selected l) (rootedSpan selected r)) [true] := by
         rw [right];exact exitArc_empty_right l r _
        rcases boundary [true] exit with ⟨y,loc⟩|loc
        · have rLeaf:r=.leaf y:=Option.some.inj loc
          right;left
          exact ⟨x,y,by rw [lLeaf,rLeaf];exact .here,hit,Or.inr ⟨[true],exit.1,exit.2.1,exit.2.2.1,exit.2.2.2,loc⟩⟩
        · have rU:r=U:=Option.some.inj loc
          right;right
          refine ⟨[],false,x,?_,hit,exit⟩
          change some (.node l r)=some (endpointForkTree false x U)
          rw [lLeaf,rU];rfl
      · rcases ir right br with ⟨y,rLeaf,hitR⟩|terminal|fork
        · exact Or.inr (Or.inl ⟨x,y,by rw [lLeaf,rLeaf];exact .here,hit,Or.inl hitR⟩)
        · exact Or.inr (Or.inl (terminal_right selected l r true _ _ terminal))
        · exact Or.inr (Or.inr (fork_right selected l r U true _ _ fork))
    · exact Or.inr (Or.inl (terminal_left selected l r true _ _ terminal))
    · exact Or.inr (Or.inr (fork_left selected l r U true _ _ fork))

theorem minimal_two_terminal_or_fork (selected : List Nat) (S U : Tree)
 (count:2≤((leaves S).filter selected.contains).length)
 (boundary:LeafOrTreeBoundary S (minimalVertices selected S) U) :
 EndpointTerminal selected S (minimalVertices selected S) ∨ EndpointFork selected S (minimalVertices selected S) U := by
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
   rcases ir cr (treeBoundary_right l r U false [] _ boundary) with terminal|fork
   · exact Or.inl (terminal_right selected l r false [] _ terminal)
   · exact Or.inr (fork_right selected l r U false [] _ fork)
  | false =>
   cases right:(rootedSpan selected r).isEmpty with
   | true =>
    have zero:=rooted_empty_selected_count_zero selected r right
    have cl:2≤((leaves l).filter selected.contains).length := by
     simpa only [leaves,List.filter_append,List.length_append,zero,Nat.add_zero] using count
    have frame:minimalVertices selected (.node l r)=vertexFrame false (minimalVertices selected l) [] := by
     simp only [minimalVertices,left,right,Bool.false_eq_true,ite_false,ite_true,vertexFrame,prependSide,List.map_nil,List.nil_append,List.append_nil]
    rw [frame] at boundary ⊢
    rcases il cl (treeBoundary_left l r U false _ [] boundary) with terminal|fork
    · exact Or.inl (terminal_left selected l r false _ [] terminal)
    · exact Or.inr (fork_left selected l r U false _ [] fork)
   | false =>
    have frame:minimalVertices selected (.node l r)=vertexFrame true (rootedSpan selected l) (rootedSpan selected r) := by
     simp only [minimalVertices,left,right,Bool.false_eq_true,ite_false,vertexFrame,ite_true,List.singleton_append]
    rw [frame] at boundary ⊢
    have nl:rootedSpan selected l≠[] := by intro e;rw [e] at left;cases left
    have nr:rootedSpan selected r≠[] := by intro e;rw [e] at right;cases right
    rcases rooted_terminal_fork_or_leaf selected l U nl (treeBoundary_left l r U true _ _ boundary) with ⟨x,lLeaf,hit⟩|terminal|fork
    · rcases rooted_terminal_fork_or_leaf selected r U nr (treeBoundary_right l r U true _ _ boundary) with ⟨y,rLeaf,hitR⟩|terminal|fork
      · exact Or.inl ⟨x,y,by rw [lLeaf,rLeaf];exact .here,hit,Or.inl hitR⟩
      · exact Or.inl (terminal_right selected l r true _ _ terminal)
      · exact Or.inr (fork_right selected l r U true _ _ fork)
    · exact Or.inl (terminal_left selected l r true _ _ terminal)
    · exact Or.inr (fork_left selected l r U true _ _ fork)

end PaidBuilderAuthor

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @PaidBuilderAuthor.root_vertex_member
#print axioms PaidBuilderAuthor.root_vertex_member
#check @PaidBuilderAuthor.vertices_left_member
#print axioms PaidBuilderAuthor.vertices_left_member
#check @PaidBuilderAuthor.vertices_right_member
#print axioms PaidBuilderAuthor.vertices_right_member
#check @PaidBuilderAuthor.exitArc_left
#print axioms PaidBuilderAuthor.exitArc_left
#check @PaidBuilderAuthor.exitArc_right
#print axioms PaidBuilderAuthor.exitArc_right
#check @PaidBuilderAuthor.treeBoundary_left
#print axioms PaidBuilderAuthor.treeBoundary_left
#check @PaidBuilderAuthor.treeBoundary_right
#print axioms PaidBuilderAuthor.treeBoundary_right
#check @PaidBuilderAuthor.exitArc_empty_left
#print axioms PaidBuilderAuthor.exitArc_empty_left
#check @PaidBuilderAuthor.exitArc_empty_right
#print axioms PaidBuilderAuthor.exitArc_empty_right
#check @PaidBuilderAuthor.fork_left
#print axioms PaidBuilderAuthor.fork_left
#check @PaidBuilderAuthor.fork_right
#print axioms PaidBuilderAuthor.fork_right
#check @PaidBuilderAuthor.rooted_terminal_fork_or_leaf
#print axioms PaidBuilderAuthor.rooted_terminal_fork_or_leaf
#check @PaidBuilderAuthor.minimal_two_terminal_or_fork
#print axioms PaidBuilderAuthor.minimal_two_terminal_or_fork
