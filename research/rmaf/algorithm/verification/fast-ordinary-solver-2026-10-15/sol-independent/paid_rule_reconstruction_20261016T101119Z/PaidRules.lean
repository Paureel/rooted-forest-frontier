/- Exact conditional paid-rule interfaces. Named geometric premises are OPEN. -/
import PaidConsumerV2
open RMAF ForestState OutputState Universal233 Universal233.CherryBranching OrdinaryDispatch
open OrdinaryDispatch.FastOrdinary
namespace IndependentPaid

def OnePendantExchange : Prop := ∀T S p a b,
 DepthOne.proper T S=true → CoreGraph.CherryAt T p a b → (cuts S a b).length=1 →
 ∀F,agreement T S F=true → ∃H,agreement T S H=true ∧ H.length≤F.length ∧
 VertexGeometry.Refines H (pendantPartition S a b)

def CherryForestDichotomy : Prop := ∀T S p a b,
 DepthOne.proper T S=true → CoreGraph.CherryAt T p a b → ∀F,agreement T S F=true →
 [a]∈F ∨ [b]∈F ∨ VertexGeometry.Refines F (pendantPartition S a b)

theorem singleton_refines {T S : Tree} {F : Forest} {a : Nat}
 (ns : (leaves S).Nodup) (hF : agreement T S F=true) (ha : [a]∈F) :
 VertexGeometry.Refines F (singletonPartition S a) := by
 have part := hF
 simp only [agreement,Bool.and_eq_true] at part
 have source := part.1.1.1.2
 have flat := (IndependentCommon.flatten_from_partition _ F ns source).symm.nodup ns
 have labels : ∀B∈F,∀x∈B,x∈leaves S := by
  have check := source
  simp only [partitionCheck,Bool.and_eq_true] at check
  intro B hB x hx
  exact List.contains_iff_mem.1 (List.all_eq_true.1 check.2 x (List.mem_flatten.2 ⟨B,hB,hx⟩))
 intro B hB
 by_cases aB : a∈B
 · have eq : B=[a] := shared_block_equal flat hB ha aB (by simp)
   subst B
   exact ⟨[a],by simp [singletonPartition],fun _ hx=>hx⟩
 · refine ⟨(leaves S).filter (fun x=>x != a),by simp [singletonPartition],?_⟩
   intro x hx
   have xa : x≠a := fun e=>aB (e ▸ hx)
   simp [labels B hB x hx,xa]

/- Source partition/embedding checks are the explicitly reused branch_checks.
The sourceForest equality and literal payment shapes are definitions. -/
theorem literal_branches {T S : Tree} {p : Vertex} {a b : Nat}
 (hp : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T p a b) :
 Literal S (branches S a b) := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts hp
 intro c hc
 obtain ⟨part,emb,paid⟩ := branch_checks nt ns (fun x=>perm.mem_iff) ch hc
 refine ⟨part,emb,paid,?_⟩
 have cases : c=singletonChild S a ∨ c=singletonChild S b ∨ c=pendantChild S a b := by
  simpa only [branches,List.mem_cons,List.mem_singleton] using hc
 rcases cases with rfl|rfl|rfl <;> rfl

theorem positive_branches {S : Tree} {a b : Nat} (positive : 1≤(cuts S a b).length) :
 ∀c∈branches S a b,1≤c.paid := by
 intro c hc
 have cases : c=singletonChild S a ∨ c=singletonChild S b ∨ c=pendantChild S a b := by
  simpa only [branches,List.mem_cons,List.mem_singleton] using hc
 rcases cases with rfl|rfl|rfl
 · exact Nat.le_refl _
 · exact Nat.le_refl _
 · exact positive

theorem query_reverse_own {T S : Tree} {q : Nat} {answer : Option CommonForest}
 (h : QueryExact S T q answer) : QueryExact T S q answer := by
 cases answer with
 | none =>
  intro F hF
  exact h F (IndependentGeometry.agreement_swap hF)
 | some F =>
  refine ⟨IndependentGeometry.agreement_swap h.1,h.2.1,?_⟩
  intro G hG
  exact h.2.2 G (IndependentGeometry.agreement_swap hG)

theorem oriented_query_own {T S : Tree} {q : Nat} {reverse : Bool} {answer : Option CommonForest}
 (h : QueryExact (Oriented reverse T S).1 (Oriented reverse T S).2 q answer) : QueryExact T S q answer := by
 cases reverse
 · exact h
 · exact query_reverse_own h

theorem one_rule_if_exchange (exchange : OnePendantExchange) : IndependentReconstruction.OneRule := by
 intro q T S reverse c proper _ selected below
 have reflection := early_sound T S
 rw [selected] at reflection
 have hp := IndependentCommon.oriented_proper_own proper reverse
 have ch := (selected_actual reflection).1
 have one : (cuts (Oriented reverse T S).2 c.a c.b).length=1 := by
  rw [←(selected_actual reflection).2]
  exact (selected_spec reflection).2.1
 have litAll := literal_branches hp ch
 have lit : Literal (Oriented reverse T S).2 [pendantChild (Oriented reverse T S).2 c.a c.b] := by
  intro child hc
  have eq : child=pendantChild (Oriented reverse T S).2 c.a c.b := by simpa using hc
  subst child
  exact litAll _ (by simp [branches])
 have positive : ∀child∈[pendantChild (Oriented reverse T S).2 c.a c.b],1≤child.paid := by
  intro child hc
  have eq : child=pendantChild (Oriented reverse T S).2 c.a c.b := by simpa using hc
  subst child
  change 1≤(cuts (Oriented reverse T S).2 c.a c.b).length
  omega
 apply oriented_query_own (reverse:=reverse)
 apply checked_caller_from_strict hp lit positive below
 intro F hF
 obtain ⟨H,hH,len,ref⟩ := exchange _ _ _ _ _ hp ch one F hF
 exact ⟨pendantChild (Oriented reverse T S).2 c.a c.b,by simp,H,⟨hH,ref⟩,len⟩

theorem high_rule_if_dichotomy (dichotomy : CherryForestDichotomy) : IndependentReconstruction.HighRule := by
 intro q T S reverse c proper _ selected below
 have reflection := early_sound T S
 rw [selected] at reflection
 have hp := IndependentCommon.oriented_proper_own proper reverse
 have ch := (selected_actual reflection).1
 have high : 3≤(cuts (Oriented reverse T S).2 c.a c.b).length := by
  rw [←(selected_actual reflection).2]
  exact (selected_spec reflection).2.1
 have ns := (IndependentReconstruction.proper_parts hp).2.1
 apply oriented_query_own (reverse:=reverse)
 apply checked_caller_from_strict hp (literal_branches hp ch) (positive_branches (by omega)) below
 intro F hF
 rcases dichotomy _ _ _ _ _ hp ch F hF with ha|hb|ref
 · exact ⟨singletonChild (Oriented reverse T S).2 c.a,by simp [branches],F,
    ⟨hF,singleton_refines ns hF ha⟩,Nat.le_refl _⟩
 · exact ⟨singletonChild (Oriented reverse T S).2 c.b,by simp [branches],F,
    ⟨hF,singleton_refines ns hF hb⟩,Nat.le_refl _⟩
 · exact ⟨pendantChild (Oriented reverse T S).2 c.a c.b,by simp [branches],F,
    ⟨hF,ref⟩,Nat.le_refl _⟩

theorem solver_if_paid_geometry (exchange : OnePendantExchange) (dichotomy : CherryForestDichotomy)
 (forward4 : IndependentReconstruction.ForwardRule4) (reverse4 : IndependentReconstruction.ReverseRule4)
 (hard : IndependentReconstruction.Hard2Rule) (nonrefusal : IndependentReconstruction.RejectImpossible)
 (q : Nat) : ∀T S,DepthOne.proper T S=true → QueryExact T S q (FastOrdinary.solve q T S) :=
 IndependentGeometry.solver_after_common_geometry (one_rule_if_exchange exchange)
  (high_rule_if_dichotomy dichotomy) forward4 reverse4 hard nonrefusal q
end IndependentPaid
