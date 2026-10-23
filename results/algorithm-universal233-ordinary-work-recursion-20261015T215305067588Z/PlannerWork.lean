import CallDecrease
namespace Universal233.BothBad
open RMAF CoreProgram CoreWork SourceCoverage PairAssembly BinaryCheap RankConsumer

theorem entries_length (q : Nat) (mode : Mode) (xs : List Output) :
    (entries q mode xs).length≤xs.length := List.length_filterMap_le _ _

theorem cheapPlan_length (S T : Tree) (A B C D : List Nat) (q : Nat)
    (xs ys : List Output) : (cheapPlan S T A B C D q xs ys).length≤xs.length+ys.length := by
  cases hg : restrictionAgrees S T (ay A D) && restrictionAgrees S T (an A D) with
  | false =>
    have hx := entries_length q .ordinary xs
    have hy := entries_length q .full ys
    simp [cheapPlan,hg,List.length_append]
    omega
  | true =>
    cases hk : knownOne T S A with
    | none => simp [cheapPlan,hg,hk]
    | some F =>
      have hx := entries_length q .ordinary xs
      have hy := entries_length q (.retained A B C F) ys
      simp [cheapPlan,hg,hk,List.length_append]
      omega

theorem generate_length_bound (S : Tree) (color : Nat → Nat) (q : Nat) :
    (generate S color q).outputs.length≤3*2^(q+1) := by
  unfold generate
  split
  · have h := run_records_bound (min q ((leaves S).length-1)) (fromTree color [] S) [] []
    have pow := Nat.pow_le_pow_right (n:=2) (by decide)
      (show min q ((leaves S).length-1)+1≤q+1 by omega)
    simp only [records] at h
    omega
  · simp

theorem plan_length_bound (S T : Tree) (A B C : List Nat)
    (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (hl : ∀ x, x∈leaves S → x∈leaves T)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (hchoose : PairGeometry.choose T A B=some (.edge edge)) :
    (plan S T A B C (PairGeometry.descendants T edge.2) q).length≤6*2^(q+1) := by
  let D := PairGeometry.descendants T edge.2
  have ra := selected_ranks S T A B C edge ht hl hp hchoose
  have ga := generate_length_bound S (cheapColor A B D) q
  have gb := generate_length_bound S (cheapColor B A D) q
  change (plan S T A B C D q).length≤_
  by_cases hq : q<3
  · simp [plan,hq]
  · have aexact := reuse_exact S (cheapColor A B D) hs ra.1 q (by omega)
    have bexact := reuse_exact S (cheapColor B A D) hs ra.2 q (by omega)
    by_cases ha : (fourProbe S (cheapColor A B D)).outputs.isEmpty=true
    · by_cases hb : (fourProbe S (cheapColor B A D)).outputs.isEmpty=true
      · have he := entries_length q .full ((generate S (cheapColor A B D) q).outputs++(generate S (cheapColor B A D) q).outputs)
        simp only [List.length_append] at he
        simpa [plan,hq,ha,hb] using (show
          (entries q .full ((generate S (cheapColor A B D) q).outputs++(generate S (cheapColor B A D) q).outputs)).length≤6*2^(q+1) by omega)
      · have eqB : (fourProbe S (cheapColor B A D)).outputs=(generate S (cheapColor B A D) q).outputs := by
          simpa [reuse,hb] using bexact
        have h := cheapPlan_length S T B A C D q (fourProbe S (cheapColor B A D)).outputs
          (reuse S (cheapColor A B D) (fourProbe S (cheapColor A B D)).outputs q)
        rw [eqB,aexact] at h
        have bound : (cheapPlan S T B A C D q (generate S (cheapColor B A D) q).outputs
          (generate S (cheapColor A B D) q).outputs).length≤6*2^(q+1) := by omega
        unfold plan
        rw [ite_eq_right hq]
        dsimp only
        rw [ite_eq_left ha,ite_eq_right hb,eqB,aexact]
        exact bound
    · have eqA : (fourProbe S (cheapColor A B D)).outputs=(generate S (cheapColor A B D) q).outputs := by
        simpa [reuse,ha] using aexact
      have h := cheapPlan_length S T A B C D q (fourProbe S (cheapColor A B D)).outputs
        (reuse S (cheapColor B A D) (fourProbe S (cheapColor B A D)).outputs q)
      rw [eqA,bexact] at h
      have bound : (cheapPlan S T A B C D q (generate S (cheapColor A B D) q).outputs
        (generate S (cheapColor B A D) q).outputs).length≤6*2^(q+1) := by omega
      unfold plan
      rw [ite_eq_right hq]
      dsimp only
      rw [ite_eq_right ha,eqA,bexact]
      exact bound

structure CoreRequest where
  color : Nat → Nat
  budget : Nat

/-- Literal core evaluations in the planner's source order. The list is a
source billing trace; evaluating this accounting function is not a new solver. -/
def coreRequests (S : Tree) (A B D : List Nat) (q : Nat) : List CoreRequest :=
  if q<3 then [] else
    let ca := cheapColor A B D
    let cb := cheapColor B A D
    let a := (fourProbe S ca).outputs
    let b := (fourProbe S cb).outputs
    [⟨ca,3⟩,⟨cb,3⟩]++
      if a.isEmpty then
        if b.isEmpty then [⟨ca,q⟩,⟨cb,q⟩] else [⟨ca,q⟩]
      else if b.isEmpty then [⟨cb,q⟩] else []

theorem coreRequests_length (S : Tree) (A B D : List Nat) (q : Nat) :
    (coreRequests S A B D q).length≤4 := by
  unfold coreRequests
  split
  · simp
  · dsimp only
    split
    · split <;> simp only [List.length_append,List.length_cons,List.length_nil] <;> omega
    · split <;> simp only [List.length_append,List.length_cons,List.length_nil] <;> omega

theorem coreRequests_budget (S : Tree) (A B D : List Nat) (q : Nat) :
    ∀ r∈coreRequests S A B D q, r.budget≤q := by
  intro r hr
  unfold coreRequests at hr
  split at hr
  · simp at hr
  · rename_i hq
    dsimp only at hr
    split at hr
    · split at hr <;> simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr <;> grind
    · split at hr <;> simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr <;> grind

def coreEnvelope (S : Tree) (q : Nat) : Nat :=
  initialCharge S+(cap (inputResource S)+6)*(q+1)*2^(q+1)

theorem core_work_envelope (S : Tree) (r : CoreRequest) (q : Nat) (hr : r.budget≤q) :
    (meterGenerate S r.color r.budget).measured.work≤coreEnvelope S q := by
  have h := generate_work_bound S r.color r.budget
  have small : min r.budget ((leaves S).length-1)+1≤q+1 := by omega
  have pow := Nat.pow_le_pow_right (n:=2) (by decide) small
  have first := Nat.mul_le_mul_left (cap (inputResource S)+6) small
  have prod := Nat.mul_le_mul first pow
  exact Nat.le_trans h (Nat.add_le_add_left prod _)

def corePrefixBill (S : Tree) (A B D : List Nat) (q : Nat) : Nat :=
  ((coreRequests S A B D q).map (fun r => (meterGenerate S r.color r.budget).measured.work)).sum

theorem corePrefixBill_bound (S : Tree) (A B D : List Nat) (q : Nat) :
    corePrefixBill S A B D q≤4*coreEnvelope S q := by
  have aux (xs : List CoreRequest) (h : ∀ r∈xs, r.budget≤q) :
      (xs.map (fun r => (meterGenerate S r.color r.budget).measured.work)).sum≤xs.length*coreEnvelope S q := by
    induction xs with
    | nil => simp
    | cons r xs ih =>
      have a := core_work_envelope S r q (h r (by simp))
      have b := ih (fun z hz => h z (by simp [hz]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  exact Nat.le_trans (aux _ (coreRequests_budget S A B D q))
    (Nat.mul_le_mul_right _ (coreRequests_length S A B D q))
end Universal233.BothBad
