import GeneralPendantCoreR3
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair ContactedSource
namespace ContactedForward

theorem span_ext_own (A B : List Nat) (same : ∀x,A.contains x=B.contains x) (T : Tree) :
 rootedSpan A T=rootedSpan B T := by
 induction T with
 | leaf x => change (if A.contains x then [[]] else [])=(if B.contains x then [[]] else []);rw [same x]
 | node l r il ir =>
  change (if (rootedSpan A l).isEmpty && (rootedSpan A r).isEmpty then [] else []::(prependSide false (rootedSpan A l)++prependSide true (rootedSpan A r)))=_
  rw [il,ir]
  rfl

theorem minimal_ext_own (A B : List Nat) (same : ∀x,A.contains x=B.contains x) (T : Tree) :
 minimalVertices A T=minimalVertices B T := by
 induction T with
 | leaf x => change (if A.contains x then [[]] else [])=(if B.contains x then [[]] else []);rw [same x]
 | node l r il ir =>
  change (if (rootedSpan A l).isEmpty then prependSide true (minimalVertices A r) else
   if (rootedSpan A r).isEmpty then prependSide false (minimalVertices A l) else
    []::(prependSide false (rootedSpan A l)++prependSide true (rootedSpan A r)))=_
  rw [span_ext_own A B same l,span_ext_own A B same r,il,ir]
  rfl

theorem cuts_swap_own (S : Tree) (a b : Nat) : cuts S a b=cuts S b a := by
 have same : ∀x,([a,b] : List Nat).contains x=([b,a] : List Nat).contains x := by
  intro x;simp only [List.contains_cons,List.contains_nil,Bool.or_false,Bool.false_or,Bool.or_comm]
 change (vertices S).filter (fun v=>!v.isEmpty && (minimalVertices [a,b] S).contains v.dropLast && !(minimalVertices [a,b] S).contains v)=_
 rw [minimal_ext_own [a,b] [b,a] same S]
 rfl

theorem literal_partition_perm_own (S : Tree) {C D : List Vertex} (perm : C.Perm D) :
 (Rule4.literalPartition S C).Perm (Rule4.literalPartition S D) := by
 have core : (leaves S).filter (fun x=>C.all (fun q=>!(subtreeLabels S q).contains x))=
  (leaves S).filter (fun x=>D.all (fun q=>!(subtreeLabels S q).contains x)) := by
  congr 1
  funext x
  exact perm.all_eq
 exact (perm.map (subtreeLabels S)).append (by rw [core])

theorem literal_pendant_eq (S : Tree) (a b : Nat) :
 Rule4.literalPartition S (cuts S a b)=pendantPartition S a b := by
 unfold Rule4.literalPartition pendantPartition coreLabels
 congr 1
 congr 1
 congr 1
 funext x
 apply Bool.eq_iff_iff.2
 simp only [List.all_eq_true,Bool.not_eq_true',←Bool.not_eq_true,List.contains_iff_mem]
 constructor
 · intro no hit
   obtain ⟨X,hmap,hx⟩ := List.mem_flatten.1 hit
   obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hmap
   exact no q hq hx
 · intro no q hq hx
   exact no (List.mem_flatten.2 ⟨_,List.mem_map.2 ⟨q,hq,rfl⟩,hx⟩)

theorem merge_full_all {T S : Tree} {G : List (List Nat)} {a b z : Nat}
 (proper : DepthOne.proper T S=true) (ch : HasCherry a b T) (fresh : z∉leaves T)
 (hG : agreement T S G=true) (ref : VertexGeometry.Refines G (pendantPartition S a b))
 (singleton : [b]∈G) :
 agreement T S (mergeCommon a b z G)=true ∧
 (mergeCommon a b z G).length+1≤G.length ∧
 VertexGeometry.Refines (mergeCommon a b z G) (pendantPartition S a b) := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts proper
 have selfProper : DepthOne.proper T T=true := by
  simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using And.intro nt (And.intro nt (List.Perm.refl _))
 have target := common_singleton_merge ch ch selfProper fresh G (agreement_target_self hG) singleton
 have source := source_merge_all proper ch fresh hG ref singleton
 have targetChecks := target.1
 simp only [agreement,Bool.and_eq_true] at targetChecks
 have flat := IndependentCommon.flatten_from_partition _ _ nt targetChecks.1.1.1.1
 have sourcePartition := IndependentCommon.partition_from_flatten _ _ ns
  (partition_nonempty targetChecks.1.1.1.1) (flat.trans perm)
 refine ⟨?_,target.2.1,source.2⟩
 simp only [agreement,Bool.and_eq_true]
 exact ⟨⟨⟨⟨targetChecks.1.1.1.1,sourcePartition⟩,source.1.1⟩,targetChecks.1.2⟩,source.1.2⟩

end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.span_ext_own
#print axioms ContactedForward.span_ext_own
#check @ContactedForward.minimal_ext_own
#print axioms ContactedForward.minimal_ext_own
#check @ContactedForward.cuts_swap_own
#print axioms ContactedForward.cuts_swap_own
#check @ContactedForward.literal_partition_perm_own
#print axioms ContactedForward.literal_partition_perm_own
#check @ContactedForward.literal_pendant_eq
#print axioms ContactedForward.literal_pendant_eq
#check @ContactedForward.merge_full_all
#print axioms ContactedForward.merge_full_all
