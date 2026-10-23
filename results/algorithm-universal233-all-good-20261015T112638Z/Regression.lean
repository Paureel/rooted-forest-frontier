import ColorClasses

namespace Universal233.RankDichotomy.Regression
open RMAF CoreProgram SourceCoverage VertexGeometry

def quartet : Tree := CoreProgram.Controls.crossed
def contiguous (x : Nat) : Nat := if x < 2 then 0 else 1
def crossed (x : Nat) : Nat := x % 2

theorem contiguous_feasible : RankFeasible quartet contiguous := by
  refine ⟨[[0,1],[2,3]],by decide,by decide,?_,by decide⟩
  simp [LabelMonochromatic,contiguous]
  constructor <;> intro x y hx hy <;> grind

theorem generic_unique_contiguous (q : Nat) (hq : 1 ≤ q) :
    ∃ o, (generate quartet contiguous q).outputs = [o] ∧ o.sourceCuts.length = 1 ∧
      ∀ b, b ∈ o.partition → ∀ y, y ∈ b ↔ y ∈ leaves quartet ∧
        contiguous y = contiguous (b.headD 0) := by
  exact feasible_unique_color_classes quartet contiguous (by decide) contiguous_feasible q hq

theorem crossed_infeasible : ¬RankFeasible quartet crossed := by
  intro hf
  obtain ⟨o,ho,hcost⟩ := feasible_unique quartet crossed (by decide) hf 3 (by decide)
  have hlen := congrArg List.length ho
  have hc : (generate quartet crossed 3).outputs.length = 2 := by decide
  simp only [List.length_singleton] at hlen
  omega

theorem generic_crossed_mass (b : Rat) (hb : 2 ≤ b) :
    rawQMass b (generate quartet crossed 3).outputs ≤ 2*b^(-2 : Int) :=
  infeasible_mass quartet crossed 3 crossed_infeasible b hb

theorem generic_crossed_cost (o : Output) (ho : o ∈ (generate quartet crossed 3).outputs) :
    2 ≤ o.sourceCuts.length := infeasible_cost quartet crossed 3 crossed_infeasible o ho

end Universal233.RankDichotomy.Regression
