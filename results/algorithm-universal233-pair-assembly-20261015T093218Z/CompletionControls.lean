import HardPaid
import AssemblyControls

namespace Universal233.PaidAssembly.Controls
open RMAF CoreProgram SourceCoverage VertexGeometry
open Universal233.Assembly.Controls

theorem control_hard_named_original_cover :
    ∃ o, o ∈ WholeSourceMass.cliqueOutputs HardParent.source4 HardParent.target4 [2] [3] [] 2 ∧
      OutputWitness HardParent.source4 [[2],[3],[0,1]] [[0,1],[2],[3]] 2 o ∧
      CliqueClearing HardParent.target4 o.partition [2] [3] [0,1] [] := by
  have hl : ∀ x, x ∈ leaves HardParent.source4 → x ∈ leaves HardParent.target4 := by
    intro x hx; simpa [HardParent.source4,HardParent.target4,leaves,or_comm,or_left_comm,or_assoc] using hx
  have h := hard2_clique_named_cover HardParent.target4 HardParent.source4 [[0,1],[2],[3]] [] 2
    (by decide) (by decide) hl HardParent.control_clean_agreement
    (z := [false]) (a := 0) (b := 1) rfl HardParent.control_root_lca_cuts
    (by simp [HardParent.target4,selectedLeaves,Join]) (by decide)
  rcases h.2.2 with ha | hb | h
  · simp at ha
  · simp at hb
  · exact h

theorem control_hard_endpoint_alternative :
    [0] ∈ [[0],[1],[2],[3]] ∧ agreement HardParent.target4 HardParent.source4 [[0],[1],[2],[3]] = true := by decide

theorem control_clique_same_list :
    (∃ o, o ∈ WholeSourceMass.cliqueOutputs cliqueS cliqueT ca cb v 5 ∧
      OutputWitness cliqueS [ca,cb,cc] (singles cliqueS) 5 o ∧ CliqueClearing cliqueT o.partition ca cb cc v) ∧
    rawQMass (mkRat 233 100) (WholeSourceMass.cliqueOutputs cliqueS cliqueT ca cb v 5) ≤
      3*(mkRat 233 100)^(-4 : Int) := by
  apply clique_paid_cover cliqueT cliqueS ca cb cc (singles cliqueS) v 5
    (by decide) (by decide) clique_labels (by decide) (by decide)
  · exact singles_refine cliqueS ca cb cc (by decide)
  · simp [cliqueT,v,selectedLeaves,Join]
  · decide
  · decide
  · decide
  · decide
  · decide

theorem control_four_same_list :
    (∃ o, o ∈ WholeSourceMass.fourChainOutputs chainS chainT ba bb v w 6 ∧
      OutputWitness chainS [ba,bb,bc] (singles chainS) 6 o ∧ FourClearing chainT o.partition ba bb bc v w) ∧
    rawQMass (mkRat 233 100) (WholeSourceMass.fourChainOutputs chainS chainT ba bb v w 6) ≤
      4*(mkRat 233 100)^(-4 : Int) := by
  apply four_paid_cover chainT chainS ba bb bc (singles chainS) v w 6
    (by decide) (by decide) chain_labels (by decide) (by decide)
  · exact singles_refine chainS ba bb bc (by decide)
  · simp [chainT,v,selectedLeaves,Join]
  · simp [chainT,w,selectedLeaves,Join]
  · decide
  · decide
  · decide
  · decide
  · exact Nat.le_of_eq chain_joint_three.symm
  · decide
  · decide

theorem control_diagonal_same_list :
    (∃ o, o ∈ WholeSourceMass.diagonalOutputs diagS diagT da db v w 5 ∧
      OutputWitness diagS [da,db,dc] (singles diagS) 5 o ∧ DiagonalClearing diagT o.partition da db dc v w) ∧
    rawQMass (mkRat 233 100) (WholeSourceMass.diagonalOutputs diagS diagT da db v w 5) ≤
      (mkRat 233 100)^(-3 : Int)+(mkRat 233 100)^(-4 : Int) := by
  apply diagonal_paid_cover diagT diagS da db dc (singles diagS) v w 5
    (by decide) (by decide) diag_labels (by decide) (by decide)
  · exact singles_refine diagS da db dc (by decide)
  · simp [diagT,v,selectedLeaves,Join]
  · simp [diagT,w,selectedLeaves,Join]
  · decide
  · decide
  · decide
  · decide
  · exact diag_joint_two
  · decide
  · decide

theorem control_literal_diagonal_costs :
    (WholeSourceMass.diagonalOutputs diagS diagT da db v w 5).map (fun o => o.sourceCuts.length) = [3,4] := by decide

theorem control_literal_zero_budget : WholeSourceMass.cliqueOutputs cliqueS cliqueT ca cb v 0 = [] := by decide

theorem control_source_forest_is_not_target_agreement :
    ((generate HardParent.source4 (fun _ => 0) 0).outputs.all
      (fun o => agreement HardParent.target4 HardParent.source4 o.partition)) = false := by decide

private theorem private_origin_control : (mkRat 233 100) ≥ 2 := by decide

theorem control_private_origin_consumer : (mkRat 233 100) ≥ 2 := private_origin_control
end Universal233.PaidAssembly.Controls
