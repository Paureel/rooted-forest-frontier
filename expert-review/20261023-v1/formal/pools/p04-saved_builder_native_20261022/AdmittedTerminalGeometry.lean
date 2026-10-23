import AdmittedRemainingPartition
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CoreGraph Universal233.HardParent

-- A literal boundary predicate; no SourceSpine/Attachment specification is used.
def LeafBoundary (S : Tree) (M : List Vertex) : Prop :=
 ∀v,v∈Universal233.HardParent.vertices S → v≠[] → v.dropLast∈M → v∉M →
  ∃x,subtree S v=some (.leaf x)

def vertexFrame (root : Bool) (A B : List Vertex) : List Vertex :=
 (if root then [[]] else [])++(prependSide false A++prependSide true B)

theorem frame_left_mem (root : Bool) (A B : List Vertex) (v : Vertex) :
 (false::v)∈vertexFrame root A B ↔ v∈A := by
 cases root <;> simp [vertexFrame,prependSide]

theorem frame_right_mem (root : Bool) (A B : List Vertex) (v : Vertex) :
 (true::v)∈vertexFrame root A B ↔ v∈B := by
 cases root <;> simp [vertexFrame,prependSide]

theorem leafBoundary_left (l r : Tree) (root : Bool) (A B : List Vertex)
 (boundary : LeafBoundary (.node l r) (vertexFrame root A B)) : LeafBoundary l A := by
 intro v member nonempty parent outside
 have drop:(false::v).dropLast=false::v.dropLast := by
  cases v with | nil => contradiction | cons x xs => rfl
 have valid:(false::v)∈Universal233.HardParent.vertices (.node l r) := by
  simp [Universal233.HardParent.vertices,prependSide,member]
 have parent':(false::v).dropLast∈vertexFrame root A B := by
  rw [drop];exact (frame_left_mem root A B v.dropLast).mpr parent
 have outside':(false::v)∉vertexFrame root A B := by
  intro h;exact outside ((frame_left_mem root A B v).mp h)
 exact boundary (false::v) valid (by intro h;cases h) parent' outside'

theorem leafBoundary_right (l r : Tree) (root : Bool) (A B : List Vertex)
 (boundary : LeafBoundary (.node l r) (vertexFrame root A B)) : LeafBoundary r B := by
 intro v member nonempty parent outside
 have drop:(true::v).dropLast=true::v.dropLast := by
  cases v with | nil => contradiction | cons x xs => rfl
 have valid:(true::v)∈Universal233.HardParent.vertices (.node l r) := by
  simp [Universal233.HardParent.vertices,prependSide,member]
 have parent':(true::v).dropLast∈vertexFrame root A B := by
  rw [drop];exact (frame_right_mem root A B v.dropLast).mpr parent
 have outside':(true::v)∉vertexFrame root A B := by
  intro h;exact outside ((frame_right_mem root A B v).mp h)
 exact boundary (true::v) valid (by intro h;cases h) parent' outside'

theorem leafBoundary_empty_left (l r : Tree) (B : List Vertex)
 (boundary : LeafBoundary (.node l r) (vertexFrame true [] B)) : ∃x,l=.leaf x := by
 have rootL:[]∈Universal233.HardParent.vertices l := by
  cases l <;> simp only [Universal233.HardParent.vertices,List.mem_cons_self]
 have valid:[false]∈Universal233.HardParent.vertices (.node l r) := by
  simpa [Universal233.HardParent.vertices,prependSide] using rootL
 have parent:[false].dropLast∈vertexFrame true [] B := by exact List.mem_cons_self
 have outside:[false]∉vertexFrame true [] B := by simp [frame_left_mem]
 obtain ⟨x,eq⟩:=boundary [false] valid (by intro h;cases h) parent outside
 exact ⟨x,Option.some.inj eq⟩

theorem leafBoundary_empty_right (l r : Tree) (A : List Vertex)
 (boundary : LeafBoundary (.node l r) (vertexFrame true A [])) : ∃x,r=.leaf x := by
 have rootR:[]∈Universal233.HardParent.vertices r := by
  cases r <;> simp only [Universal233.HardParent.vertices,List.mem_cons_self]
 have valid:[true]∈Universal233.HardParent.vertices (.node l r) := by
  simpa [Universal233.HardParent.vertices,prependSide] using rootR
 have parent:[true].dropLast∈vertexFrame true A [] := by exact List.mem_cons_self
 have outside:[true]∉vertexFrame true A [] := by simp [frame_right_mem]
 obtain ⟨x,eq⟩:=boundary [true] valid (by intro h;cases h) parent outside
 exact ⟨x,Option.some.inj eq⟩

theorem rooted_empty_selected_count_zero (selected : List Nat) (S : Tree)
 (empty:(rootedSpan selected S).isEmpty=true) :
 ((leaves S).filter selected.contains).length=0 := by
 induction S with
 | leaf x =>
  change (if selected.contains x then [[]] else []).isEmpty=true at empty
  simp only [leaves,List.filter_cons,List.filter_nil]
  cases hit:selected.contains x with
  | false => rfl
  | true => rw [hit] at empty;cases empty
 | node l r il ir =>
  cases left:(rootedSpan selected l).isEmpty <;>
   cases right:(rootedSpan selected r).isEmpty
  all_goals try {simp [rootedSpan,left,right] at empty}
  simp only [leaves,List.filter_append,List.length_append,il left,ir right]

theorem rooted_nonempty_cherry_or_leaf (selected : List Nat) (S : Tree)
 (nonempty:rootedSpan selected S≠[])
 (boundary:LeafBoundary S (rootedSpan selected S)) :
 (∃x,S=.leaf x ∧ selected.contains x=true) ∨
 ∃x y,HasCherry x y S ∧ (selected.contains x=true ∨ selected.contains y=true) := by
 induction S with
 | leaf x =>
  cases hit:selected.contains x with
  | false =>
   apply False.elim
   apply nonempty
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
  rw [frame] at boundary
  have bl:=leafBoundary_left l r true _ _ boundary
  have br:=leafBoundary_right l r true _ _ boundary
  by_cases left:rootedSpan selected l=[]
  · have right:rootedSpan selected r≠[] := by
     intro empty
     apply nonempty
     simp [rootedSpan,left,empty]
    have leftBoundary:LeafBoundary (.node l r) (vertexFrame true [] (rootedSpan selected r)) := by
     simpa only [left] using boundary
    obtain ⟨x,lLeaf⟩:=leafBoundary_empty_left l r _ leftBoundary
    rcases ir right br with ⟨y,rLeaf,hit⟩|⟨y,z,cherry,hit⟩
    · exact Or.inr ⟨x,y,by rw [lLeaf,rLeaf];exact .here,Or.inr hit⟩
    · exact Or.inr ⟨y,z,.right cherry,hit⟩
  · rcases il left bl with ⟨x,lLeaf,hit⟩|⟨x,y,cherry,hit⟩
    · by_cases right:rootedSpan selected r=[]
      · have rightBoundary:LeafBoundary (.node l r) (vertexFrame true (rootedSpan selected l) []) := by
         simpa only [right] using boundary
        obtain ⟨y,rLeaf⟩:=leafBoundary_empty_right l r _ rightBoundary
        exact Or.inr ⟨x,y,by rw [lLeaf,rLeaf];exact .here,Or.inl hit⟩
      · rcases ir right br with ⟨y,rLeaf,hitR⟩|⟨y,z,cherry,hitR⟩
        · exact Or.inr ⟨x,y,by rw [lLeaf,rLeaf];exact .here,Or.inl hit⟩
        · exact Or.inr ⟨y,z,.right cherry,hitR⟩
    · exact Or.inr ⟨x,y,.left cherry,hit⟩

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.frame_left_mem
#print axioms AdmittedRule5Author.frame_left_mem
#check @AdmittedRule5Author.frame_right_mem
#print axioms AdmittedRule5Author.frame_right_mem
#check @AdmittedRule5Author.leafBoundary_left
#print axioms AdmittedRule5Author.leafBoundary_left
#check @AdmittedRule5Author.leafBoundary_right
#print axioms AdmittedRule5Author.leafBoundary_right
#check @AdmittedRule5Author.leafBoundary_empty_left
#print axioms AdmittedRule5Author.leafBoundary_empty_left
#check @AdmittedRule5Author.leafBoundary_empty_right
#print axioms AdmittedRule5Author.leafBoundary_empty_right
#check @AdmittedRule5Author.rooted_empty_selected_count_zero
#print axioms AdmittedRule5Author.rooted_empty_selected_count_zero
#check @AdmittedRule5Author.rooted_nonempty_cherry_or_leaf
#print axioms AdmittedRule5Author.rooted_nonempty_cherry_or_leaf
