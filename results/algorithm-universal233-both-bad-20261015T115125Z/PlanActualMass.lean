import CheapPlanMass
namespace Universal233.BothBad
open RMAF CoreProgram PaidQueries SourceCoverage PairAssembly BinaryCheap RankConsumer
open VertexGeometry BinaryExchange

theorem mixed_le_four (c : Rat) (hc : 2≤c) (h3 : c≤3) :
    c^(-3 : Int)+c^(-4 : Int)≤4*c^(-4 : Int) := by
  have cp : 0<c := by grind
  have he : c^(-3 : Int)=c*c^(-4 : Int) := by
    have h := Rat.zpow_add (q:=c) (Rat.ne_of_gt cp) (m:=1) (n:=(-4 : Int))
    rw [show (1 : Int)+(-4)=(-3) by decide] at h
    simpa only [Rat.zpow_one] using h
  rw [he]
  have h := Rat.mul_le_mul_of_nonneg_right h3
    (Rat.le_of_lt (Rat.zpow_pos (a:=c) (n:=(-4 : Int)) cp))
  grind

/-- Every callback occurrence of the actual executable planner/dispatcher is
charged. This bound includes failing/early-stopped paid ordinary calls and
does not assume any recursive solver is correct. Nonrecursive source work is
a separate obligation. -/
theorem solvePair_actual_mass (solve : ForestSolver) (S T : Tree) (A B C : List Nat)
    (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (c : Rat) (hc : 2≤c) (h3 : c≤3)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x∈leaves S ↔ x∈leaves T)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (hsource : pairwiseEmbeddings S [A,B,C]=true)
    (hbadA : restrictionAgrees S T A=false) (hbadB : restrictionAgrees S T B=false)
    (hgoodC : restrictionAgrees S T C=true)
    (hchoose : PairGeometry.choose T A B=some (.edge edge))
    (hac : Disj T A C) (hbc : Disj T B C) :
    traceMass c q (solvePair solve S T A B C edge q).calls≤4*c^(-4 : Int) := by
  change traceMass c q (execute solve T S q (plan S T A B C (PairGeometry.descendants T edge.2) q)).calls≤_
  rw [execute_mass]
  let D := PairGeometry.descendants T edge.2
  change entryMass solve T S c q (plan S T A B C D q)≤_
  by_cases hq : q<3
  · simp only [plan,hq,ite_true,entryMass,List.map_nil,List.sum_nil]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c)))
  · by_cases ha : (fourProbe S (cheapColor A B D)).outputs.isEmpty=true
    · by_cases hb : (fourProbe S (cheapColor B A D)).outputs.isEmpty=true
      · have form : plan S T A B C D q=entries q .full (outputs S A B D q) := by
          simp [plan,hq,ha,hb,outputs,sideOutputs,cheapColor,WholeSourceMass.wholeOutputs]
        rw [form]
        have paid := full_entries_mass solve T S c hc q (outputs S A B D q)
        have failA : fourAccepted S (cheapColor A B D)=false := by simp only [fourAccepted,ha,Bool.not_true]
        have failB : fourAccepted S (cheapColor B A D)=false := by simp only [fourAccepted,hb,Bool.not_true]
        have high := (selected_two_high S T A B C edge hs ht (fun x hx => (same x).1 hx) hp hchoose
          failA failB q c hc).2
        exact Rat.le_trans paid high
      · have acceptB : fourAccepted S (cheapColor B A D)=true := by
          simp only [fourAccepted]
          cases h : (fourProbe S (cheapColor B A D)).outputs.isEmpty <;> simp_all
        obtain ⟨hp',hsource',hchoose'⟩ := selected_symmetry S T A B C edge ht
          (fun x hx => (same x).1 hx) hp hsource hchoose
        have bound := cheap_plan_actual_mass solve S T B A C edge q c hc hs ht same hp' hsource'
          hbadB hbadA hgoodC hchoose' hbc hac acceptB (by omega)
        apply Rat.le_trans ?_ (mixed_le_four c hc h3)
        simpa [plan,hq,ha,hb] using bound
    · have acceptA : fourAccepted S (cheapColor A B D)=true := by
        simp only [fourAccepted]
        cases h : (fourProbe S (cheapColor A B D)).outputs.isEmpty <;> simp_all
      have bound := cheap_plan_actual_mass solve S T A B C edge q c hc hs ht same hp hsource
        hbadA hbadB hgoodC hchoose hac hbc acceptA (by omega)
      apply Rat.le_trans ?_ (mixed_le_four c hc h3)
      simpa [plan,hq,ha] using bound
end Universal233.BothBad
