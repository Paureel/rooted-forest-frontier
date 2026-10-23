import AdmittedGraph
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.HardParent

theorem actual_source_embeddings (T S : Tree) (a b : Nat)
 (proper : DepthOne.proper T S=true) :
 pairwiseEmbeddings S (pendantPartition S a b)=true := by
 have h : (decide (leaves T).Nodup=true ∧ decide (leaves S).Nodup=true) ∧ decide ((leaves T).Perm (leaves S))=true := by
  simpa only [DepthOne.proper,Bool.and_eq_true] using proper
 exact source_embeddings (of_decide_eq_true h.1.2)

theorem cherries_children_to_hasCherry {l r : Tree}
 (hl : ∀p a b,(p,a,b)∈cherries l→HasCherry a b l)
 (hr : ∀p a b,(p,a,b)∈cherries r→HasCherry a b r)
 {p : RMAF.Vertex} {a b : Nat}
 (member : (p,a,b)∈(cherries l).map (fun (q,x,y)=>(false::q,x,y))++
  (cherries r).map (fun (q,x,y)=>(true::q,x,y))) : HasCherry a b (.node l r) := by
 rcases List.mem_append.mp member with left|right
 · obtain ⟨⟨q,x,y⟩,hm,eq⟩:=List.mem_map.mp left
   cases eq
   exact .left (hl q a b hm)
 · obtain ⟨⟨q,x,y⟩,hm,eq⟩:=List.mem_map.mp right
   cases eq
   exact .right (hr q a b hm)

theorem cherries_to_hasCherry (T : Tree) (p : RMAF.Vertex) (a b : Nat)
 (member : (p,a,b)∈cherries T) : HasCherry a b T := by
 induction T generalizing p a b with
 | leaf x => simp only [cherries,List.not_mem_nil] at member
 | node l r ihl ihr =>
  cases l <;> cases r
  · simp only [cherries,List.mem_singleton] at member
    cases member
    exact .here
  all_goals exact cherries_children_to_hasCherry ihl ihr member

theorem hasCherry_prop_swap {T : Tree} {a b : Nat} (h : HasCherry a b T) : HasCherry b a T := by
 induction h with
 | here => exact .swap
 | swap => exact .here
 | left h ih => exact .left ih
 | right h ih => exact .right ih

theorem hasCherry_bool_prop (T : Tree) (a b : Nat) (good : hasCherry T a b=true) : HasCherry a b T := by
 obtain ⟨⟨p,x,y⟩,hm,check⟩:=List.any_eq_true.mp good
 simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at check
 rcases check with ⟨hx,hy⟩|⟨hx,hy⟩
 · subst x;subst y;exact cherries_to_hasCherry T p a b hm
 · subst x;subst y;exact hasCherry_prop_swap (cherries_to_hasCherry T p b a hm)

theorem hasCherry_bool_ordered (T : Tree) (a b : Nat) (good : hasCherry T a b=true) :
 (a,b)∈Rule4.orderedCherries T :=
 Rule4.orderedCherries_complete (hasCherry_bool_prop T a b good)
end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.actual_source_embeddings
#print axioms AdmittedRule5Author.actual_source_embeddings
#check @AdmittedRule5Author.cherries_children_to_hasCherry
#print axioms AdmittedRule5Author.cherries_children_to_hasCherry
#check @AdmittedRule5Author.cherries_to_hasCherry
#print axioms AdmittedRule5Author.cherries_to_hasCherry
#check @AdmittedRule5Author.hasCherry_prop_swap
#print axioms AdmittedRule5Author.hasCherry_prop_swap
#check @AdmittedRule5Author.hasCherry_bool_prop
#print axioms AdmittedRule5Author.hasCherry_bool_prop
#check @AdmittedRule5Author.hasCherry_bool_ordered
#print axioms AdmittedRule5Author.hasCherry_bool_ordered
