import MassAssembly
namespace Universal233.BothBad
open RMAF CoreProgram PaidQueries SourceCoverage PairAssembly BinaryCheap RankConsumer
open VertexGeometry BinaryExchange

theorem ordinary_entries_mass (solve : ForestSolver) (T S : Tree) (c : Rat) (hc : 2≤c)
    (q : Nat) (xs : List Output) :
    entryMass solve T S c q (entries q .ordinary xs)≤rawQMass c xs := by
  have h := entries_mass_bound solve T S c hc q .ordinary xs 1 (by decide) (by
    intro o ho hb
    simp only [Mode.extra,Nat.sub_zero,Rat.mul_one]
    exact ordinary_dispatch_mass solve T S o q _ (by simp only [Mode.extra] at hb;omega) c hc)
  simpa only [Rat.mul_one] using h

theorem ordinary_paid_entries_mass (solve : ForestSolver) (T S : Tree) (c : Rat) (hc : 2≤c)
    (q : Nat) (xs : List Output) (bad : ∀ o∈xs, TwoBad S T o) :
    entryMass solve T S c q (entries q .ordinary xs)≤rawQMass c xs*c^(-1 : Int) := by
  apply entries_mass_bound solve T S c hc q .ordinary xs (c^(-1 : Int))
    (Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c)))
  intro o ho hb
  simp only [Mode.extra,Nat.sub_zero]
  exact ordinary_dispatch_paid_mass solve T S o q _ (by simp only [Mode.extra] at hb;omega) c hc (bad o ho)

theorem retained_entries_mass (solve : ForestSolver) (T S : Tree) (c : Rat) (hc : 2≤c)
    (q : Nat) (xs : List Output) (A B C : List Nat) (F : Forest) :
    entryMass solve T S c q (entries q (.retained A B C F) xs)≤rawQMass c xs*c^(-1 : Int) := by
  apply entries_mass_bound solve T S c hc q (.retained A B C F) xs (c^(-1 : Int))
    (Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c)))
  intro o ho hb
  simp only [Mode.extra]
  rw [retained_dispatch_mass solve T S o A B C F q _ (by simp only [Mode.extra] at hb;omega) c hc]
  exact Rat.le_refl

theorem cheap_plan_actual_mass (solve : ForestSolver) (S T : Tree) (A B C : List Nat)
    (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (c : Rat) (hc : 2≤c)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x∈leaves S ↔ x∈leaves T)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (hsource : pairwiseEmbeddings S [A,B,C]=true)
    (hbadA : restrictionAgrees S T A=false) (hbadB : restrictionAgrees S T B=false)
    (hgoodC : restrictionAgrees S T C=true)
    (hchoose : PairGeometry.choose T A B=some (.edge edge))
    (hac : Disj T A C) (hbc : Disj T B C)
    (haccept : fourAccepted S (cheapColor A B (PairGeometry.descendants T edge.2))=true)
    (hq : 3≤q) :
    let D := PairGeometry.descendants T edge.2
    entryMass solve T S c q (cheapPlan S T A B C D q (fourProbe S (cheapColor A B D)).outputs
        (reuse S (cheapColor B A D) (fourProbe S (cheapColor B A D)).outputs q))≤
      c^(-3 : Int)+c^(-4 : Int) := by
  dsimp only
  let D := PairGeometry.descendants T edge.2
  obtain ⟨co,hprobe,hcoCost,hcoLen,hcoPart,hcoSource,hcoTarget,hcoAll,hgood,hbad⟩ :=
    selected_cheap_facts S T A B C edge hs ht same hp hsource hbadA hbadB hgoodC hchoose hac hbc haccept
  change (fourProbe S (cheapColor A B D)).outputs=[co] at hprobe
  have ranks := selected_ranks S T A B C edge ht (fun x hx => (same x).1 hx) hp hchoose
  have opposite : reuse S (cheapColor B A D) (fourProbe S (cheapColor B A D)).outputs q=
      sideOutputs S A B D q := reuse_exact S _ hs ranks.2 q hq
  have massOpp : rawQMass c (sideOutputs S A B D q)≤c^(-3 : Int) := by
    have h := generate_rawQ_mass S (cheapColor B A D) q c hc
    change rawQMass c (sideOutputs S A B D q)≤c^(1-(RankDichotomy.inputRank S (cheapColor B A D) : Int)) at h
    rw [ranks.2] at h
    exact h
  have massCheap : rawQMass c [co]=c^(-3 : Int) := by simp [rawQMass,hcoCost,Rat.add_zero]
  have cp : 0<c := by grind
  have cn := Rat.ne_of_gt cp
  have shift : c^(-3 : Int)*c^(-1 : Int)=c^(-4 : Int) := by rw [←Rat.zpow_add cn];rfl
  cases hg : restrictionAgrees S T (ay A D) && restrictionAgrees S T (an A D) with
  | false =>
    have form : cheapPlan S T A B C D q (fourProbe S (cheapColor A B D)).outputs
        (reuse S (cheapColor B A D) (fourProbe S (cheapColor B A D)).outputs q)=
        entries q .ordinary [co] ++ entries q .full (sideOutputs S A B D q) := by
      simp [cheapPlan,hg,hprobe,opposite]
    rw [form,entryMass_append]
    have badco := hbad hg
    have ha := ordinary_paid_entries_mass solve T S c hc q [co] (by
      intro z hz
      have he : z=co := by simpa using hz
      subst z
      exact badco)
    rw [massCheap,shift] at ha
    have hb := Rat.le_trans (full_entries_mass solve T S c hc q (sideOutputs S A B D q)) massOpp
    have hh := qadd_le_add ha hb
    simpa only [Rat.add_comm] using hh
  | true =>
    obtain ⟨aout,hknown,hsafe⟩ := hgood hg
    have form : cheapPlan S T A B C D q (fourProbe S (cheapColor A B D)).outputs
        (reuse S (cheapColor B A D) (fourProbe S (cheapColor B A D)).outputs q)=
        entries q .ordinary [co] ++ entries q (.retained A B C aout.partition) (sideOutputs S A B D q) := by
      simp [cheapPlan,hg,hknown,hprobe,opposite]
    rw [form,entryMass_append]
    have ha := ordinary_entries_mass solve T S c hc q [co]
    rw [massCheap] at ha
    have hb := retained_entries_mass solve T S c hc q (sideOutputs S A B D q) A B C aout.partition
    have hmul := Rat.mul_le_mul_of_nonneg_right massOpp (Rat.le_of_lt (Rat.zpow_pos (a:=c) (n:=(-1 : Int)) cp))
    rw [shift] at hmul
    exact qadd_le_add ha (Rat.le_trans hb hmul)
end Universal233.BothBad
