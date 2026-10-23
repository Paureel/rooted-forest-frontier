import ControlFlowV4
open RMAF ForestState Universal233 Universal233.CherryBranching OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace AuthoredGlobal
-- These explicit helper premises are discharged by exact licensed stored proofs
-- at final kernel assembly. They are not additional axioms or a final theorem.
structure LocalSupport : Prop where
 found_spec : ∀T S c, DepthOne.pretest01 T S=.found c →
  DepthOne.proper T S=true ∧ c∈DepthOne.candidates S ∧ agreement T S (DepthOne.forest S c)=true ∧
  ∀d,d∈DepthOne.candidates S→agreement T S (DepthOne.forest S d)=true→DepthOne.cutCost c≤DepthOne.cutCost d
 refused_iff : ∀T S,DepthOne.pretest01 T S=.refused ↔ DepthOne.proper T S=false
 candidate_complete : ∀T S F,(leaves S).Nodup→agreement T S F=true→F.length-1≤1→
  ∃c,c∈DepthOne.candidates S ∧ agreement T S (DepthOne.forest S c)=true ∧ DepthOne.cutCost c≤F.length-1
 agreement_nonempty : ∀T S F,agreement T S F=true→F≠[]
 common_ready : ∀{T S c reverse},DepthOne.proper T S=true→
  select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.common,c)→
  DepthOne.proper (commonPair T S reverse c).1 (commonPair T S reverse c).2=true ∧
  (leaves (commonPair T S reverse c).1).length<(leaves T).length
 common_transport : ∀{T S c reverse},DepthOne.proper T S=true→
  select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.common,c)→
  ∀q answer,QueryExact (commonPair T S reverse c).1 (commonPair T S reverse c).2 q answer→
  QueryExact T S q (answer.map (expandCommon T S reverse c))
 select_none_leaf : ∀{T S},select T S=none→∃a,T=.leaf a
 leaf_not_rejected : ∀a {S},DepthOne.proper (.leaf a) S=true→DepthOne.pretest01 (.leaf a) S≠.rejected

theorem proper_parts {T S : Tree} (hp : DepthOne.proper T S=true) :
 (leaves T).Nodup ∧ (leaves S).Nodup ∧ (leaves T).Perm (leaves S) := by
 simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hp

theorem forest_cost_length (S : Tree) (c : Option RMAF.Vertex) :
 (DepthOne.forest S c).length=DepthOne.cutCost c+1 := by cases c <;> rfl

theorem found_minimum (support : LocalSupport) (T S : Tree) (c : Option RMAF.Vertex)
 (hc : DepthOne.pretest01 T S=.found c) :
 ∀F,agreement T S F=true→(DepthOne.forest S c).length≤F.length := by
 have hs:=support.found_spec T S c hc
 have nodup:=(proper_parts hs.1).2.1
 have lc:=forest_cost_length S c
 have one : DepthOne.cutCost c≤1 := by cases c <;> simp [DepthOne.cutCost]
 intro F hF
 have ne:=support.agreement_nonempty T S F hF
 have positive : 0<F.length := by cases F with | nil => exact False.elim (ne rfl) | cons A G => simp
 by_cases cheap : F.length-1≤1
 · obtain ⟨d,member,accepted,cost⟩:=support.candidate_complete T S F nodup hF cheap
   have best:=hs.2.2.2 d member accepted
   omega
 · omega

theorem found_case (support : LocalSupport) (T S : Tree) (q : Nat) (c : Option RMAF.Vertex)
 (hc : DepthOne.pretest01 T S=.found c) :
 QueryExact T S q (if DepthOne.cutCost c≤q then some (DepthOne.forest S c) else none) := by
 have hs:=support.found_spec T S c hc
 have least:=found_minimum support T S c hc
 have lc:=forest_cost_length S c
 by_cases affordable : DepthOne.cutCost c≤q
 · rw [if_pos affordable]
   change agreement T S (DepthOne.forest S c)=true ∧ (DepthOne.forest S c).length-1≤q ∧ _
   exact ⟨hs.2.2.1,by omega,least⟩
 · rw [if_neg affordable]
   change ∀F,agreement T S F=true→q<F.length-1
   intro F hF
   have min:=least F hF
   omega

theorem leaves_positive (T : Tree) : 0<(leaves T).length := by
 induction T with
 | leaf a => simp [leaves]
 | node l r il ir => simp only [leaves,List.length_append];omega

theorem tree_of_length_one (T : Tree) (hlen : (leaves T).length=1) : ∃a,T=.leaf a := by
 cases T with
 | leaf a => exact ⟨a,rfl⟩
 | node l r =>
   have hl:=leaves_positive l
   have hr:=leaves_positive r
   simp only [leaves,List.length_append] at hlen
   omega

theorem right_leaf_not_rejected (support : LocalSupport) {T : Tree} (a : Nat)
 (hp : DepthOne.proper T (.leaf a)=true) : DepthOne.pretest01 T (.leaf a)≠.rejected := by
 have perm:=(proper_parts hp).2.2
 have hlen : (leaves T).length=1 := by simpa only [leaves,List.length_singleton] using perm.length_eq
 obtain ⟨b,rfl⟩:=tree_of_length_one T hlen
 exact support.leaf_not_rejected b hp

theorem select_exists (support : LocalSupport) {T S : Tree} (hp : DepthOne.proper T S=true)
 (rejected : DepthOne.pretest01 T S=.rejected) : ∃s,select T S=some s := by
 cases selected : select T S with
 | some s => exact ⟨s,rfl⟩
 | none =>
   obtain ⟨a,rfl⟩:=support.select_none_leaf selected
   exact False.elim (support.leaf_not_rejected a hp rejected)

theorem reverse_select_exists (support : LocalSupport) {T S : Tree} (hp : DepthOne.proper T S=true)
 (rejected : DepthOne.pretest01 T S=.rejected) : ∃s,select S T=some s := by
 cases selected : select S T with
 | some s => exact ⟨s,rfl⟩
 | none =>
   obtain ⟨a,rfl⟩:=support.select_none_leaf selected
   exact False.elim (right_leaf_not_rejected support a hp rejected)

def CommonTag (T S : Tree) : Early T S→Prop
 | .common r c => select (Oriented r T S).1 (Oriented r T S).2=some (.common,c)
 | _ => True

theorem common_tag (T S : Tree) : CommonTag T S (early T S) := by
 unfold early
 repeat' first | split | simp_all [CommonTag,Oriented]

theorem common_selected {T S : Tree} {r : Bool} {c : Candidate}
 (h : early T S=.common r c) : select (Oriented r T S).1 (Oriented r T S).2=some (.common,c) := by
 have ht:=common_tag T S
 rw [h] at ht
 exact ht

theorem early_not_refused (support : LocalSupport) {T S : Tree} (hp : DepthOne.proper T S=true)
 (rejected : DepthOne.pretest01 T S=.rejected) : early T S≠.refused := by
 obtain ⟨⟨pa,ca⟩,hA⟩:=select_exists support hp rejected
 obtain ⟨⟨pb,cb⟩,hB⟩:=reverse_select_exists support hp rejected
 intro bad
 cases pa <;> cases pb <;> simp [early,hA,hB] at bad
 all_goals cases hF : Rule4.select T S <;> cases hR : Rule4.select S T <;> simp [hF,hR] at bad
end AuthoredGlobal
