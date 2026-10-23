import WholeMass

namespace Universal233.WholeSourceMass.MassControls
open RMAF VertexGeometry SourceCoverage CoreProgram

def tripod : Tree := .node (.node (.leaf 4) (.leaf 5))
  (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
def ta : List Nat := [0,2]
def tb : List Nat := [3,4]
def tc : List Nat := [5,1]

theorem tripod_call : WholeCall tripod tripod ta tb tc := by
  refine ⟨⟨?_,?_,?_,?_⟩,by decide,by intros; assumption,by decide,by decide,by decide⟩
  all_goals intro x <;> simp [tripod,ta,tb,tc,leaves] <;> omega

theorem tripod_occupied : Occupied ta tripod [true] ∧ Occupied tb tripod [true] ∧
    Occupied tc tripod [true] := by
  refine ⟨⟨by simp [tripod,selectedLeaves,Join],by decide⟩,
    ⟨by simp [tripod,selectedLeaves,Join],by decide⟩,
    ⟨by simp [tripod,selectedLeaves,Join],by decide⟩⟩

theorem literal_clique_color_count :
    (dedupNat ((leaves tripod).map
      (taggedColor ta tb (fun _ => 0) (colorLabel tripod [true]) (colorLabel tripod [true])))).length = 5 := by decide

theorem actual_clique_mass (q : Nat) (b : Rat) (hb : 2 ≤ b) :
    rawQMass b (cliqueOutputs tripod tripod ta tb [true] q) ≤ 3*b^(-4 : Int) :=
  clique_raw_mass _ _ _ _ _ tripod_call _ tripod_occupied.1
    tripod_occupied.2.1 tripod_occupied.2.2 q b hb

def chain : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
  (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5))
def ca : List Nat := [1,2]
def cb : List Nat := [0,3]
def cc : List Nat := [4,5]

theorem chain_call : WholeCall chain chain ca cb cc := by
  refine ⟨⟨?_,?_,?_,?_⟩,by decide,by intros; assumption,by decide,by decide,by decide⟩
  all_goals intro x <;> simp [chain,ca,cb,cc,leaves] <;> omega

theorem chain_joint_two : (jointColors cb chain [false] [true]).length = 2 := by decide

theorem literal_diagonal_color_counts :
    (dedupNat ((leaves chain).map
      (taggedColor ca cb (fun _ => 0) (jointLabel chain [false] [true]) (fun _ => 0)))).length = 4 ∧
    (dedupNat ((leaves chain).map
      (taggedColor ca cb (colorLabel chain [false]) (fun _ => 0) (colorLabel chain [true])))).length = 5 := by decide

theorem actual_diagonal_mass (q : Nat) (b : Rat) (hb : 2 ≤ b) :
    rawQMass b (diagonalOutputs chain chain ca cb [false] [true] q) ≤ b^(-3 : Int)+b^(-4 : Int) :=
  diagonal_raw_mass _ _ _ _ _ chain_call _ _ ⟨by simp [chain,selectedLeaves,Join],by decide⟩
    ⟨by simp [chain,selectedLeaves,Join],by decide⟩ chain_joint_two q b hb

def chain3 : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
  (.node (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5)) (.leaf 6))
def cb3 : List Nat := [0,3,6]

theorem chain3_call : WholeCall chain3 chain3 ca cb3 cc := by
  refine ⟨⟨?_,?_,?_,?_⟩,by decide,by intros; assumption,by decide,by decide,by decide⟩
  all_goals intro x <;> simp [chain3,ca,cb3,cc,leaves] <;> omega

theorem chain3_joint_three : (jointColors cb3 chain3 [false] [true,false]).length = 3 := by decide

theorem literal_four_chain_color_counts :
    (dedupNat ((leaves chain3).map
      (taggedColor ca cb3 (fun _ => 0) (colorLabel chain3 [false]) (colorLabel chain3 [true,false])))).length = 5 ∧
    (dedupNat ((leaves chain3).map
      (taggedColor ca cb3 (fun _ => 0) (jointLabel chain3 [false] [true,false]) (fun _ => 0)))).length = 5 ∧
    (dedupNat ((leaves chain3).map
      (taggedColor ca cb3 (colorLabel chain3 [false]) (fun _ => 0) (colorLabel chain3 [true,false])))).length = 5 ∧
    (dedupNat ((leaves chain3).map
      (taggedColor ca cb3 (colorLabel chain3 [false]) (colorLabel chain3 [true,false]) (fun _ => 0)))).length = 5 := by decide

theorem actual_four_chain_mass (q : Nat) (b : Rat) (hb : 2 ≤ b) :
    rawQMass b (fourChainOutputs chain3 chain3 ca cb3 [false] [true,false] q) ≤ 4*b^(-4 : Int) := by
  apply four_chain_raw_mass _ _ _ _ _ chain3_call _ _
    ⟨by simp [chain3,selectedLeaves,Join],by decide⟩
    ⟨by simp [chain3,selectedLeaves,Join],by decide⟩
    ⟨by simp [chain3,selectedLeaves,Join],by decide⟩
    ⟨by simp [chain3,selectedLeaves,Join],by decide⟩
    (by rw [chain3_joint_three]; decide) q b hb

theorem root_has_exactly_two_original_colors :
    (localColors cb (colorLabel chain [])).length = 2 := by decide

theorem empty_parent_has_zero_colors :
    (localColors [] (fun _ => 0)).length = 0 := by decide

theorem original_label_at_root_needs_nonlabel :
    colorLabel (.leaf 0) [] 0 = 3 ∧
    (localColors [0] (colorLabel (.leaf 0) [])).length = 1 := by decide

theorem raw_list_multiplicity :
    rawQMass 2 [⟨[],[[]]⟩,⟨[],[[]]⟩] = 1 := by
  simp only [rawQMass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_singleton]
  rw [Rat.zpow_neg,Rat.zpow_natCast]
  simp only [Rat.pow_one]
  have h := Rat.mul_inv_cancel (2 : Rat) (by decide)
  grind

theorem count2_does_not_allow_four_chain_rank5 :
    (dedupNat ((leaves chain).map
      (taggedColor ca cb (fun _ => 0) (jointLabel chain [false] [true]) (fun _ => 0)))).length < 5 := by decide

end Universal233.WholeSourceMass.MassControls
