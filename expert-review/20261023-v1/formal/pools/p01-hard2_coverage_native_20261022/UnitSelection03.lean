import UnitPaidCore04
import ForestComplete12
namespace UnitPaidCombination
open RMAF Universal233 Universal233.CherryBranching OrdinaryDispatch

theorem proper_parts_fresh (T S : Tree) (h : DepthOne.proper T S=true) :
    (leaves T).Nodup ∧ (leaves S).Nodup ∧ (leaves T).Perm (leaves S) := by
 simp only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at h
 exact ⟨h.1.1,h.1.2,h.2⟩

theorem local_ih_below (q r : Nat) (actual : Hard2Combine.Ordinary)
    (below : Below q actual) (strict : r<q) :
    ForestMinCompletion.LocalOrdinaryIH r actual := by
 constructor
 · intro t s b F br proper result
   have exactness:=below b (by omega) t s proper
   simpa only [result,QueryExact] using exactness
 · intro t s b G br proper hG budget
   have exactness:=below b (by omega) t s proper
   cases result : actual t s b with
   | none =>
     have absent : ∀ F,agreement t s F=true → b<F.length-1 := by
       simpa only [result,QueryExact] using exactness
     have bad:=absent G hG
     omega
   | some F => exact ⟨F,rfl⟩

theorem select_hard2_head {T S : Tree} {c : Candidate}
    (h : Universal233.CherryBranching.select T S=some (.hard2,c)) :
    (candidates T S).head?=some c := by
 unfold Universal233.CherryBranching.select at h
 dsimp only at h
 split at h
 · simp_all
 · split at h
   · simp_all
   · split at h
     · simp_all
     · cases hh : (candidates T S).head? with
       | none => simp [hh] at h
       | some d =>
         have eq : d=c := by simpa [hh] using h
         simpa [eq] using hh

theorem select_hard2_mem {T S : Tree} {c : Candidate}
    (h : Universal233.CherryBranching.select T S=some (.hard2,c)) : c∈candidates T S := by
 have hh:=select_hard2_head h
 cases hc : candidates T S with
 | nil => simp [hc] at hh
 | cons d ds =>
   have eq : d=c := by simpa [hc] using hh
   exact eq ▸ (by simp [hc])

theorem cherries_cherry {T : Tree} {p : RMAF.Vertex} {a b : Nat}
    (h : (p,a,b)∈cherries T) : CoreGraph.CherryAt T p a b := by
 induction T generalizing p a b with
 | leaf x => simp [cherries] at h
 | node l r ihl ihr =>
   have lift (hm : (p,a,b)∈
       (cherries l).map (fun (v,x,y)=>(false::v,x,y)) ++
       (cherries r).map (fun (v,x,y)=>(true::v,x,y))) :
       CoreGraph.CherryAt (.node l r) p a b := by
     rcases List.mem_append.mp hm with hl|hr
     · rcases List.mem_map.mp hl with ⟨⟨v,x,y⟩,hv,he⟩
       cases he
       simpa [CoreGraph.CherryAt,CoreGraph.subtree] using ihl hv
     · rcases List.mem_map.mp hr with ⟨⟨v,x,y⟩,hv,he⟩
       cases he
       simpa [CoreGraph.CherryAt,CoreGraph.subtree] using ihr hv
   cases l with
   | leaf x =>
     cases r with
     | leaf y =>
       have eq : (p,a,b)=([],x,y) := by simpa only [cherries,List.mem_singleton] using h
       cases eq
       rfl
     | node rl rr => apply lift;simpa only [cherries] using h
   | node ll lr =>
     cases r with
     | leaf y => apply lift;simpa only [cherries] using h
     | node rl rr => apply lift;simpa only [cherries] using h

theorem selected_cherry_fresh {T S : Tree} {c : Candidate}
    (h : Universal233.CherryBranching.select T S=some (.hard2,c)) :
    CoreGraph.CherryAt T c.parent c.a c.b := by
 have hm:=select_hard2_mem h
 unfold candidates at hm
 rcases List.mem_map.mp hm with ⟨⟨p,a,b⟩,hch,eq⟩
 cases eq
 exact cherries_cherry hch

theorem subtree_nodup_fresh {T U : Tree} {p : RMAF.Vertex}
    (nt : (leaves T).Nodup) (h : CoreGraph.subtree T p=some U) : (leaves U).Nodup := by
 induction p generalizing T with
 | nil =>
   have eq : T=U := by simpa [CoreGraph.subtree] using h
   simpa [←eq] using nt
 | cons side p ih =>
   cases T with
   | leaf x => simp [CoreGraph.subtree] at h
   | node l r =>
     change (leaves l++leaves r).Nodup at nt
     cases side with
     | false => exact ih (List.nodup_append.mp nt).1 (by simpa [CoreGraph.subtree] using h)
     | true => exact ih (List.nodup_append.mp nt).2.1 (by simpa [CoreGraph.subtree] using h)

theorem subtree_labels_fresh {T U : Tree} {p : RMAF.Vertex}
    (h : CoreGraph.subtree T p=some U) {x : Nat} (hx : x∈leaves U) : x∈leaves T := by
 induction p generalizing T with
 | nil =>
   have eq : T=U := by simpa [CoreGraph.subtree] using h
   simpa [eq] using hx
 | cons side p ih =>
   cases T with
   | leaf y => simp [CoreGraph.subtree] at h
   | node l r =>
     change x∈leaves l++leaves r
     cases side with
     | false => exact List.mem_append_left _ (ih (by simpa [CoreGraph.subtree] using h))
     | true => exact List.mem_append_right _ (ih (by simpa [CoreGraph.subtree] using h))

theorem cherry_guards_fresh {T : Tree} {p : RMAF.Vertex} {a b : Nat}
    (nt : (leaves T).Nodup) (h : CoreGraph.CherryAt T p a b) :
    a∈leaves T ∧ b∈leaves T ∧ a≠b := by
 have nd:=subtree_nodup_fresh nt h
 refine ⟨subtree_labels_fresh h (by simp [leaves]),subtree_labels_fresh h (by simp [leaves]),?_⟩
 simpa [leaves] using nd
end UnitPaidCombination

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @UnitPaidCombination.proper_parts_fresh
#print axioms UnitPaidCombination.proper_parts_fresh
#check @UnitPaidCombination.local_ih_below
#print axioms UnitPaidCombination.local_ih_below
#check @UnitPaidCombination.select_hard2_head
#print axioms UnitPaidCombination.select_hard2_head
#check @UnitPaidCombination.select_hard2_mem
#print axioms UnitPaidCombination.select_hard2_mem
#check @UnitPaidCombination.cherries_cherry
#print axioms UnitPaidCombination.cherries_cherry
#check @UnitPaidCombination.selected_cherry_fresh
#print axioms UnitPaidCombination.selected_cherry_fresh
#check @UnitPaidCombination.subtree_nodup_fresh
#print axioms UnitPaidCombination.subtree_nodup_fresh
#check @UnitPaidCombination.subtree_labels_fresh
#print axioms UnitPaidCombination.subtree_labels_fresh
#check @UnitPaidCombination.cherry_guards_fresh
#print axioms UnitPaidCombination.cherry_guards_fresh
