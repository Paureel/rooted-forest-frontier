import CohabitCoverageR3
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair ContactedSource
namespace ContactedForward

theorem leaf_address_sound_own (S : Tree) (a : Nat) : ∀p,Rule4.leafAddress a S=some p→CoreGraph.subtree S p=some (.leaf a) := by
 induction S with
 | leaf x =>
  intro p hp
  by_cases eq : x=a
  · subst x
    have ep : []=p := Option.some.inj (by simpa only [Rule4.leafAddress,ite_true] using hp)
    subst p;rfl
  · simp only [Rule4.leafAddress,eq,ite_false] at hp;cases hp
 | node l r il ir =>
  intro p hp
  cases left : Rule4.leafAddress a l with
  | some q =>
   have eq : false::q=p := Option.some.inj (by simpa only [Rule4.leafAddress,left] using hp)
   subst p;exact il _ left
  | none =>
   cases right : Rule4.leafAddress a r with
   | none => simp only [Rule4.leafAddress,left,right,Option.map_none] at hp;cases hp
   | some q =>
    have eq : true::q=p := Option.some.inj (by simpa only [Rule4.leafAddress,left,right,Option.map_some] using hp)
    subst p;exact ir _ right

theorem leaf_address_exists_own (S : Tree) (a : Nat) (ha : a∈leaves S) : ∃p,Rule4.leafAddress a S=some p := by
 induction S with
 | leaf x =>
  have eq : a=x := by simpa only [leaves,List.mem_singleton] using ha
  subst x;exact ⟨[],by simp only [Rule4.leafAddress,ite_true]⟩
 | node l r il ir =>
  cases left : Rule4.leafAddress a l with
  | some p => exact ⟨false::p,by simp only [Rule4.leafAddress,left]⟩
  | none =>
   have ar : a∈leaves r := by
    rcases List.mem_append.1 ha with al|ar
    · obtain ⟨p,hp⟩ := il al;rw [left] at hp;cases hp
    · exact ar
   obtain ⟨p,hp⟩ := ir ar
   exact ⟨true::p,by simp only [Rule4.leafAddress,left,hp,Option.map_some]⟩

theorem actual_a_head {T S : Tree} (s : Rule4.Choice T S) :
 CoreGraph.subtree S (Rule4.aHead s)=some (.leaf s.raw.a) ∧
 subtreeLabels S (Rule4.aHead s)=[s.raw.a] ∧ Rule4.aHead s≠[] := by
 have ch := ordered_sound_own S _ _ (choice_admission_own s).2.1
 obtain ⟨p,hp⟩ := leaf_address_exists_own S _ (IndependentCommon.syntax_labels ch).1
 have sub : CoreGraph.subtree S (Rule4.aHead s)=some (.leaf s.raw.a) := by
  simpa only [Rule4.aHead,hp,Option.getD_some] using leaf_address_sound_own S _ p hp
 refine ⟨sub,by rw [subtree_labels_lookup sub];rfl,?_⟩
 intro root
 rw [root] at sub
 have eq : S=.leaf s.raw.a := Option.some.inj sub
 exact IndependentCommon.syntax_not_leaf ch _ eq

theorem isolated_refines {T S : Tree} (s : Rule4.Choice T S) {F : List (List Nat)}
 (hF : agreement T S F=true) (single : [s.raw.a]∈F) :
 VertexGeometry.Refines F (Rule4.literalPartition S [Rule4.aHead s]) := by
 have proper := choice_proper s
 have checks := hF
 simp only [agreement,Bool.and_eq_true] at checks
 have labels := partition_labels checks.1.1.1.2
 have head := (actual_a_head s).2.1
 simp only [Rule4.literalPartition,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
  List.all_cons,List.all_nil,Bool.and_true,head]
 intro B hb
 by_cases yes : s.raw.a∈B
 · have eq := singleton_block_eq proper hF single hb yes
   exact ⟨[s.raw.a],List.mem_cons_self,fun x hx=>eq ▸ hx⟩
 · refine ⟨(leaves S).filter (fun x=>![s.raw.a].contains x),List.mem_cons_of_mem _ List.mem_cons_self,?_⟩
   intro x hx
   refine List.mem_filter.2 ⟨labels B hb x hx,?_⟩
   have ne : x≠s.raw.a := fun eq=>yes (eq ▸ hx)
   simpa only [Bool.not_eq_true',←Bool.not_eq_true,List.contains_iff_mem,List.mem_singleton] using ne

end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.leaf_address_sound_own
#print axioms ContactedForward.leaf_address_sound_own
#check @ContactedForward.leaf_address_exists_own
#print axioms ContactedForward.leaf_address_exists_own
#check @ContactedForward.actual_a_head
#print axioms ContactedForward.actual_a_head
#check @ContactedForward.isolated_refines
#print axioms ContactedForward.isolated_refines
