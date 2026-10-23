import Rule4Program
import FinalWork

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

abbrev Forest := List (List Nat)

def ChildFeasible (b : Branch) (r : Nat) (F : Forest) : Prop :=
  ForestState.agrees (some b.target) b.sourceForest F = true ∧
    ForestState.additionalCost b.sourceForest F ≤ r

/-- Exact, CHILD-SPECIFIC solver IH on the actual literal ForestState.
No Rule4 safety/exchange/reconstruction/mass field is supplied by the caller. -/
def ExactChild (child : Branch → Nat → Option Forest) (b : Branch) (r : Nat) : Prop :=
  (∀ G, child b r = some G → ChildFeasible b r G ∧
    ∀ H, ChildFeasible b r H → G.length ≤ H.length) ∧
  (∀ H, ChildFeasible b r H → ∃ G, child b r = some G ∧ G.length ≤ H.length)

def childOutputs (b : Branch) (q : Nat) (child : Branch → Nat → Option Forest) : List Forest :=
  if b.cost ≤ q then (child b (q-b.cost)).toList else []

def outputs {T S : Tree} (s : Choice T S) (q : Nat) (child : Branch → Nat → Option Forest) : List Forest :=
  (branches s).flatMap (fun b => childOutputs b q child)

def solveForest {T S : Tree} (s : Choice T S) (q : Nat) (child : Branch → Nat → Option Forest) : Option Forest :=
  RMAF.best List.length (fun _ => true) (outputs s q child)

def solveCuts {T S : Tree} (s : Choice T S) (q : Nat) (child : Branch → Nat → Option Forest) : Option CoreProgram.Output :=
  (solveForest s q child).bind (FinalCutRecovery.recover S)

theorem branch_original_iff {T S : Tree} (s : Choice T S) (b : Branch)
    (hb : b ∈ branches s) (F : Forest) :
    agreement b.target b.source F = true ↔ agreement T S F = true := by
  simp only [branches,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl
  · rfl
  · rfl
  · exact ⟨agreement_reverse,agreement_reverse⟩

theorem refinement_length (L : List Nat) (F Q : Forest)
    (hF : partitionCheck L F = true) (hQ : partitionCheck L Q = true)
    (href : RestrictionBridge.Refines F Q) : Q.length ≤ F.length := by
  have positive : ∀ U ∈ Q, 0 < (RestrictionBridge.family U F).length := by
    intro U hU
    exact List.length_pos_iff.2 (RestrictionBridge.family_nonempty L F Q hF hQ href U hU)
  have hs := RestrictionBridge.sum_sub_one Q (fun U => (RestrictionBridge.family U F).length) positive
  have ht := RestrictionBridge.total_family_length L F Q hF hQ href
  omega

theorem original_nonempty {T S : Tree} (s : Choice T S) (F : Forest)
    (hF : agreement T S F = true) : 0 < F.length := by
  have ha := (hasCherry_labels (orderedCherries_sound s.admission.1)).1
  obtain ⟨B,hB,_⟩ := partitionCheck_covers _ F (agreement_parts T S F hF).1 s.raw.a ha
  exact List.length_pos_of_mem hB

theorem output_sound {T S : Tree} (s : Choice T S) (q : Nat)
    (child : Branch → Nat → Option Forest)
    (ih : ∀ b, b ∈ branches s → b.cost ≤ q → ExactChild child b (q-b.cost))
    (G : Forest) (hG : G ∈ outputs s q child) :
    agreement T S G = true ∧ G.length - 1 ≤ q := by
  obtain ⟨b,hb,hout⟩ := List.mem_flatMap.1 hG
  have hex : b.cost ≤ q ∧ child b (q-b.cost) = some G := by
    unfold childOutputs at hout
    split at hout
    · exact ⟨by assumption,Option.mem_toList.1 hout⟩
    · simp at hout
  have hstate := (ih b hb hex.1).1 G hex.2
  have data := selected_source_state s b hb G
  have original := data.2.2.2.2.2.1.1 hstate.1.1
  have hlen := refinement_length (leaves b.source) G b.partition
    (source_agreement_checks original.1).1 data.1 original.2
  have hcost := data.2.2.1
  have hadd := data.2.2.2.2.2.2
  have hbudget := hstate.1.2
  rw [hadd] at hbudget
  refine ⟨(branch_original_iff s b hb G).1 original.1,?_⟩
  omega

theorem outputs_complete {T S : Tree} (s : Choice T S) (q : Nat)
    (child : Branch → Nat → Option Forest)
    (ih : ∀ b, b ∈ branches s → b.cost ≤ q → ExactChild child b (q-b.cost))
    (F : Forest) (hF : agreement T S F = true) (hbudget : F.length-1 ≤ q) :
    ∃ G, G ∈ outputs s q child ∧ G.length ≤ F.length := by
  obtain ⟨H,b,hb,hH,hlen,href⟩ := selected_branches_cover s hF
  have data := selected_source_state s b hb H
  have hbranch := (branch_original_iff s b hb H).2 hH
  have hstate := data.2.2.2.2.2.1.2 ⟨hbranch,href⟩
  have hHL : b.partition.length ≤ H.length := refinement_length (leaves b.source) H b.partition
    (source_agreement_checks hbranch).1 data.1 href
  have hcost := data.2.2.1
  have hpos := original_nonempty s F hF
  have hguard : b.cost ≤ q := by omega
  have hadditional : ForestState.additionalCost b.sourceForest H ≤ q-b.cost := by
    rw [data.2.2.2.2.2.2]
    omega
  obtain ⟨G,hG,hmin⟩ := (ih b hb hguard).2 H ⟨hstate,hadditional⟩
  refine ⟨G,?_,Nat.le_trans hmin hlen⟩
  apply List.mem_flatMap.2
  exact ⟨b,hb,by simp [childOutputs,hguard,hG]⟩

/-- A minimum original agreement is returned under only the printed exact
child-specific IH. The universal cover and source-state facts are PROVED above. -/
theorem solveForest_minimum {T S : Tree} (s : Choice T S) (q : Nat)
    (child : Branch → Nat → Option Forest)
    (ih : ∀ b, b ∈ branches s → b.cost ≤ q → ExactChild child b (q-b.cost))
    (G : Forest) (hG : solveForest s q child = some G) :
    agreement T S G = true ∧ G.length-1 ≤ q ∧
    ∀ F, agreement T S F = true → F.length-1 ≤ q → G.length ≤ F.length := by
  have hs := RMAF.best_spec List.length (fun _ : Forest => true) (outputs s q child) G hG
  have sound := output_sound s q child ih G hs.1
  refine ⟨sound.1,sound.2,?_⟩
  intro F hF hbudget
  obtain ⟨H,hH,hlen⟩ := outputs_complete s q child ih F hF hbudget
  exact Nat.le_trans (hs.2.2 H hH rfl) hlen

theorem solveForest_exists {T S : Tree} (s : Choice T S) (q : Nat)
    (child : Branch → Nat → Option Forest)
    (ih : ∀ b, b ∈ branches s → b.cost ≤ q → ExactChild child b (q-b.cost))
    (F : Forest) (hF : agreement T S F = true) (hbudget : F.length-1 ≤ q) :
    ∃ G, solveForest s q child = some G := by
  obtain ⟨G,hG,_⟩ := outputs_complete s q child ih F hF hbudget
  exact RMAF.best_exists List.length (fun _ : Forest => true) _ G hG rfl

/-- Once minimum original labels are selected, recover exactly |G|-1 original
source cuts and complete original residual components. No local cut union. -/
theorem solveCuts_original {T S : Tree} (s : Choice T S) (q : Nat)
    (child : Branch → Nat → Option Forest)
    (ih : ∀ b, b ∈ branches s → b.cost ≤ q → ExactChild child b (q-b.cost))
    (G : Forest) (hG : solveForest s q child = some G) :
    ∃ o, solveCuts s q child = some o ∧ agreement T S o.partition = true ∧
      o.sourceCuts.length = G.length-1 ∧ o.sourceCuts.length ≤ q ∧
      CutRealization.RealizedOutput S o ∧
      (∀ F, agreement T S F = true → F.length-1 ≤ q → o.partition.length ≤ F.length) := by
  obtain ⟨hagree,hbudget,hmin⟩ := solveForest_minimum s q child ih G hG
  obtain ⟨o,ho,hO,hcuts,hlen,hreal,_⟩ := FinalCutRecovery.recover_original_agreement T S G s.priority.2.1 hagree
  exact ⟨o,by simp [solveCuts,hG,ho],hO,hcuts,by omega,hreal,
    by intro F hF hFb; rw [hlen]; exact hmin F hF hFb⟩
end Universal233.Rule4

namespace Universal233.Rule4
open RMAF

theorem actual_cost_profile {T S : Tree} (s : Choice T S) :
    (branches s).map Branch.cost = costs T S s := rfl

theorem actual_callback_decrease {T S : Tree} (s : Choice T S) (q : Nat)
    (b : Branch) (hb : b ∈ branches s) (hq : b.cost ≤ q) : q-b.cost < q := by
  have hp := (selected_cut_properties s b hb).2.2.2.2.2
  omega

theorem actual_callback_mass {T S : Tree} (s : Choice T S) (q : Nat)
    (c : Rat) (hc : 2 ≤ c) :
    callbackMass c q ((branches s).map Branch.cost) ≤ c ^ (-1 : Int)+2*c ^ (-2 : Int) := by
  rw [actual_cost_profile]
  exact selected_callback_mass s c hc q

theorem solveForest_none_iff {T S : Tree} (s : Choice T S) (q : Nat)
    (child : Branch → Nat → Option Forest)
    (ih : ∀ b, b ∈ branches s → b.cost ≤ q → ExactChild child b (q-b.cost)) :
    solveForest s q child = none ↔
      ¬∃ F, agreement T S F = true ∧ F.length-1 ≤ q := by
  constructor
  · intro hn ⟨F,hF,hbudget⟩
    obtain ⟨G,hG⟩ := solveForest_exists s q child ih F hF hbudget
    rw [hn] at hG
    contradiction
  · intro hn
    cases hs : solveForest s q child with
    | none => rfl
    | some F =>
      have hf := solveForest_minimum s q child ih F hs
      exact False.elim (hn ⟨F,hf.1,hf.2.1⟩)
end Universal233.Rule4

namespace Universal233.Rule4
open RMAF

/-- Pay the actual formal final recovery once, separately from the polynomial
per-node label-selection toll. Its proved c^q bound is retained explicitly. -/
theorem solveCuts_recovery_work {T S : Tree} (s : Choice T S) (q : Nat)
    (child : Branch → Nat → Option Forest)
    (ih : ∀ b, b ∈ branches s → b.cost ≤ q → ExactChild child b (q-b.cost))
    (G : Forest) (hG : solveForest s q child = some G) (c : Rat) (hc : 2 ≤ c) :
    ((FinalCutRecovery.meterRecover S G).work : Rat) ≤
      (FinalCutRecovery.finalPolynomial S G : Rat)*c^q := by
  have hs := solveForest_minimum s q child ih G hG
  have checks := HardParent.source_agreement_checks hs.1
  exact FinalCutRecovery.final_work_absorbed S G s.priority.2.1 checks.1 checks.2 q hs.2.1 c hc
end Universal233.Rule4
