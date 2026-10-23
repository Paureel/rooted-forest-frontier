import AdmittedRemainingScans
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent Universal233.Rule5Classification

theorem source_labels_of_subtree (S : Tree) (v : Vertex) (U : Tree)
 (location : subtree S v=some U) : subtreeLabels S v=leaves U := by
 induction v generalizing S with
 | nil =>
  change some S=some U at location
  cases Option.some.inj location
  rfl
 | cons side rest ih =>
  cases S with
  | leaf x => cases location
  | node l r => cases side <;> exact ih _ location

theorem tree_leaf_count_positive (S : Tree) : 0<(leaves S).length := by
 induction S with
 | leaf x => exact Nat.zero_lt_succ 0
 | node l r il ir =>
  change 0<(leaves l++leaves r).length
  rw [List.length_append]
  omega

theorem tree_one_leaf (S : Tree) (one : (leaves S).length=1) :
 ∃x,S=.leaf x := by
 cases S with
 | leaf x => exact ⟨x,rfl⟩
 | node l r =>
  have left:=tree_leaf_count_positive l
  have right:=tree_leaf_count_positive r
  change (leaves l++leaves r).length=1 at one
  rw [List.length_append] at one
  omega

theorem tree_two_leaves (S : Tree) (two : (leaves S).length=2) :
 ∃x y,S=.node (.leaf x) (.leaf y) := by
 cases S with
 | leaf x => change 1=2 at two;cases two
 | node l r =>
  have left:=tree_leaf_count_positive l
  have right:=tree_leaf_count_positive r
  change (leaves l++leaves r).length=2 at two
  rw [List.length_append] at two
  have oneL : (leaves l).length=1:=by omega
  have oneR : (leaves r).length=1:=by omega
  obtain ⟨x,eqL⟩:=tree_one_leaf l oneL
  obtain ⟨y,eqR⟩:=tree_one_leaf r oneR
  exact ⟨x,y,by rw [eqL,eqR]⟩

theorem remaining_good_valid_cut_is_leaf (T S : Tree) (a b : Nat)
 (noLarge : selectLarge T S a b=none) (noTwo : selectSizeTwo T S a b=none)
 (e : Vertex) (member : e∈cuts S a b)
 (good : restrictionAgrees T S (subtreeLabels S e)=true)
 (valid : Valid S e) : ∃x,subtree S e=some (.leaf x) := by
 obtain ⟨U,location⟩:=valid
 have labels:=source_labels_of_subtree S e U location
 have small:=selectLarge_none_good_small T S a b noLarge e member good
 rw [labels] at small
 have positive:=tree_leaf_count_positive U
 have oneOrTwo : (leaves U).length=1 ∨ (leaves U).length=2:=by omega
 rcases oneOrTwo with one|two
 · obtain ⟨x,eq⟩:=tree_one_leaf U one
   exact ⟨x,by rw [eq] at location;exact location⟩
 · obtain ⟨x,y,eq⟩:=tree_two_leaves U two
   have forbidden:=selectSizeTwo_none_no_good_cherry T S a b noTwo e x y member good
   rw [eq] at location
   exact False.elim (forbidden location)

theorem enumerated_vertex_valid (S : Tree) (v : Vertex)
 (member : v∈Universal233.HardParent.vertices S) : Valid S v := by
 induction S generalizing v with
 | leaf x =>
  change v∈[[]] at member
  have eq:=List.mem_singleton.mp member
  subst v
  exact ⟨.leaf x,rfl⟩
 | node l r il ir =>
  change v∈[]::(prependSide false (Universal233.HardParent.vertices l)++
   prependSide true (Universal233.HardParent.vertices r)) at member
  rcases List.mem_cons.mp member with eq|member
  · subst v
    exact ⟨.node l r,rfl⟩
  · rcases List.mem_append.mp member with inLeft|inRight
    · obtain ⟨w,hw,eq⟩:=List.mem_map.mp inLeft
      subst v
      obtain ⟨U,location⟩:=il w hw
      exact ⟨U,location⟩
    · obtain ⟨w,hw,eq⟩:=List.mem_map.mp inRight
      subst v
      obtain ⟨U,location⟩:=ir w hw
      exact ⟨U,location⟩

theorem actual_cut_valid (S : Tree) (a b : Nat) (e : Vertex)
 (member : e∈cuts S a b) : Valid S e := by
 apply enumerated_vertex_valid S e
 change e∈(Universal233.HardParent.vertices S).filter _ at member
 exact (List.mem_filter.mp member).1

theorem remaining_good_cut_is_leaf (T S : Tree) (a b : Nat)
 (noLarge : selectLarge T S a b=none) (noTwo : selectSizeTwo T S a b=none)
 (e : Vertex) (member : e∈cuts S a b)
 (good : restrictionAgrees T S (subtreeLabels S e)=true) :
 ∃x,subtree S e=some (.leaf x) :=
 remaining_good_valid_cut_is_leaf T S a b noLarge noTwo e member good
  (actual_cut_valid S a b e member)

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.source_labels_of_subtree
#print axioms AdmittedRule5Author.source_labels_of_subtree
#check @AdmittedRule5Author.tree_leaf_count_positive
#print axioms AdmittedRule5Author.tree_leaf_count_positive
#check @AdmittedRule5Author.tree_one_leaf
#print axioms AdmittedRule5Author.tree_one_leaf
#check @AdmittedRule5Author.tree_two_leaves
#print axioms AdmittedRule5Author.tree_two_leaves
#check @AdmittedRule5Author.remaining_good_valid_cut_is_leaf
#print axioms AdmittedRule5Author.remaining_good_valid_cut_is_leaf
#check @AdmittedRule5Author.enumerated_vertex_valid
#print axioms AdmittedRule5Author.enumerated_vertex_valid
#check @AdmittedRule5Author.actual_cut_valid
#print axioms AdmittedRule5Author.actual_cut_valid
#check @AdmittedRule5Author.remaining_good_cut_is_leaf
#print axioms AdmittedRule5Author.remaining_good_cut_is_leaf
