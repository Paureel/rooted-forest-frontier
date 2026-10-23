import ForwardCoverageR3
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair ContactedSource
namespace ContactedForward

theorem span_at_subtree {S U : Tree} {p : Vertex} {A : List Nat} (sub : CoreGraph.subtree S p=some U) :
 ∀r,p++r∈rootedSpan A S→r∈rootedSpan A U := by
 induction p generalizing S with
 | nil =>
  have eq : S=U := Option.some.inj sub
  subst S;intro r hr;exact hr
 | cons side rest ih =>
  cases S with
  | leaf x => simp only [CoreGraph.subtree] at sub;cases sub
  | node l r =>
   intro tail h
   cases side
   · exact ih sub _ (span_child A l r false _ h)
   · exact ih sub _ (span_child A l r true _ h)

theorem common_leaf_paths {S U V : Tree} {p q : Vertex} {x : Nat}
 (nd : (leaves S).Nodup) (up : CoreGraph.subtree S p=some U) (vq : CoreGraph.subtree S q=some V)
 (xu : x∈leaves U) (xv : x∈leaves V) :
 (∃r,q=p++r) ∨ (∃r,p=q++r) := by
 induction p generalizing S q with
 | nil => exact Or.inl ⟨q,rfl⟩
 | cons side rest ih =>
  cases q with
  | nil => exact Or.inr ⟨side::rest,rfl⟩
  | cons bit tail =>
   cases S with
   | leaf y => simp only [CoreGraph.subtree] at up;cases up
   | node l r =>
    have ns := List.nodup_append.1 nd
    cases side <;> cases bit
    · rcases ih ns.1 up vq with ⟨t,eq⟩|⟨t,eq⟩
      · exact Or.inl ⟨t,congrArg (false::·) eq⟩
      · exact Or.inr ⟨t,congrArg (false::·) eq⟩
    · exact False.elim (ns.2.2 x (subtree_leaves_own (show CoreGraph.subtree l rest=some U from up) x xu) x (subtree_leaves_own (show CoreGraph.subtree r tail=some V from vq) x xv) rfl)
    · exact False.elim (ns.2.2 x (subtree_leaves_own (show CoreGraph.subtree l tail=some V from vq) x xv) x (subtree_leaves_own (show CoreGraph.subtree r rest=some U from up) x xu) rfl)
    · rcases ih ns.2.1 up vq with ⟨t,eq⟩|⟨t,eq⟩
      · exact Or.inl ⟨t,congrArg (true::·) eq⟩
      · exact Or.inr ⟨t,congrArg (true::·) eq⟩

theorem no_nested_pendant {S U : Tree} {a b : Nat} {p q : Vertex}
 (pcut : p∈cuts S a b) (qcut : q∈cuts S a b) (sub : CoreGraph.subtree S p=some U)
 {tail : Vertex} (eq : q=p++tail) (ne : tail≠[]) : False := by
 have absent := pendant_subtree_absent_endpoints pcut sub
 have empty : rootedSpan [a,b] U=[] := by
  apply span_absent U [a,b]
  intro x hx sel
  rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using sel : x=a∨x=b) with rfl|rfl
  · exact absent.1 hx
  · exact absent.2 hx
 have flags := (List.mem_filter.1 qcut).2
 simp only [Bool.and_eq_true] at flags
 have parent := minimal_in_span S [a,b] _ (List.contains_iff_mem.1 flags.1.2)
 rw [eq,List.dropLast_append_of_ne_nil ne] at parent
 have inside := span_at_subtree sub _ parent
 rw [empty] at inside
 cases inside

theorem pendant_clades_disjoint {S U V : Tree} {a b : Nat} {p q : Vertex}
 (nd : (leaves S).Nodup) (pcut : p∈cuts S a b) (qcut : q∈cuts S a b) (different : p≠q)
 (up : CoreGraph.subtree S p=some U) (vq : CoreGraph.subtree S q=some V) :
 ∀x∈leaves U,x∉leaves V := by
 intro x xu xv
 rcases common_leaf_paths nd up vq xu xv with ⟨tail,eq⟩|⟨tail,eq⟩
 · have ne : tail≠[] := by intro nil;rw [nil,List.append_nil] at eq;exact different eq.symm
   exact no_nested_pendant pcut qcut up eq ne
 · have ne : tail≠[] := by intro nil;rw [nil,List.append_nil] at eq;exact different eq
   exact no_nested_pendant qcut pcut vq eq ne

theorem vertices_nodup_own (S : Tree) : (vertices S).Nodup := by
 induction S with
 | leaf x => exact List.nodup_cons.2 ⟨List.not_mem_nil,.nil⟩
 | node l r il ir =>
  apply List.nodup_cons.2
  constructor
  · intro member
    rcases List.mem_append.1 member with left|right
    · obtain ⟨v,hv,eq⟩ := List.mem_map.1 left;cases eq
    · obtain ⟨v,hv,eq⟩ := List.mem_map.1 right;cases eq
  · apply List.nodup_append.2
    refine ⟨?_,?_,?_⟩
    · exact List.Pairwise.map (false::·) (fun _ _ ne eq=>ne (List.cons.inj eq).2) il
    · exact List.Pairwise.map (true::·) (fun _ _ ne eq=>ne (List.cons.inj eq).2) ir
    · intro p hp q hq eq
      obtain ⟨v,hv,ep⟩ := List.mem_map.1 hp
      obtain ⟨w,hw,eq'⟩ := List.mem_map.1 hq
      rw [←ep,←eq'] at eq
      cases eq

theorem cuts_nodup_own (S : Tree) (a b : Nat) : (cuts S a b).Nodup :=
 List.Pairwise.filter _ (vertices_nodup_own S)

end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.span_at_subtree
#print axioms ContactedForward.span_at_subtree
#check @ContactedForward.common_leaf_paths
#print axioms ContactedForward.common_leaf_paths
#check @ContactedForward.no_nested_pendant
#print axioms ContactedForward.no_nested_pendant
#check @ContactedForward.pendant_clades_disjoint
#print axioms ContactedForward.pendant_clades_disjoint
#check @ContactedForward.vertices_nodup_own
#print axioms ContactedForward.vertices_nodup_own
#check @ContactedForward.cuts_nodup_own
#print axioms ContactedForward.cuts_nodup_own
