import ChainAssembly
namespace Universal233.Assembly.Controls
open RMAF CoreProgram SourceCoverage VertexGeometry

def singles (s : Tree) := (leaves s).map fun x => [x]

theorem singles_refine (s : Tree) (A B C : List Nat)
    (hp : partitionCheck (leaves s) [A,B,C] = true) : RefinesBlocks (singles s) [A,B,C] := by
  intro b hb
  obtain ⟨x,hx,rfl⟩ := List.mem_map.1 hb
  rcases parent_cover s A B C hp x hx with ha | hb | hc
  · refine ⟨A,by simp,?_⟩
    intro y hy
    have he : y = x := by simpa using hy
    subst y
    exact ha
  · refine ⟨B,by simp,?_⟩
    intro y hy
    have he : y = x := by simpa using hy
    subst y
    exact hb
  · refine ⟨C,by simp,?_⟩
    intro y hy
    have he : y = x := by simpa using hy
    subst y
    exact hc

def cliqueT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 4) (.leaf 5)))
def cliqueS : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.node (.leaf 1) (.leaf 4)) (.node (.leaf 3) (.leaf 5)))
def ca : List Nat := [0,2]
def cb : List Nat := [1,4]
def cc : List Nat := [3,5]
def v : RMAF.Vertex := [true]
def w : RMAF.Vertex := [true,true]

theorem clique_labels : ∀ x, x ∈ leaves cliqueS → x ∈ leaves cliqueT := by
  intro x hx; simpa [cliqueS,cliqueT,leaves,or_assoc,or_comm,or_left_comm] using hx

theorem clique_original_cover :
    BranchSolution cliqueT cliqueS ca cb cc (singles cliqueS) 5 .keep (.at v) (.at v) ∨
    BranchSolution cliqueT cliqueS ca cb cc (singles cliqueS) 5 (.at v) .keep (.at v) ∨
    BranchSolution cliqueT cliqueS ca cb cc (singles cliqueS) 5 (.at v) (.at v) .keep := by
  apply clique_actual_cover cliqueT cliqueS ca cb cc (singles cliqueS) v 5
    (by decide) (by decide) clique_labels (by decide) (by decide)
  · intro x hx hy; simp [ca,cb] at *; omega
  · intro x hx hy; simp [ca,cc] at *; omega
  · intro x hx hy; simp [cb,cc] at *; omega
  · exact singles_refine cliqueS ca cb cc (by decide)
  · simp [cliqueT,v,selectedLeaves,Join]
  · decide

def literalCosts (s t : Tree) (A B : List Nat) (a b c : Request) (q : Nat) :=
  (generate s (requestedColor t A B a b c) q).outputs.map fun o => o.sourceCuts.length

theorem clique_literal_costs :
    literalCosts cliqueS cliqueT ca cb .keep (.at v) (.at v) 5 = [4] ∧
    literalCosts cliqueS cliqueT ca cb (.at v) .keep (.at v) 5 = [4] ∧
    literalCosts cliqueS cliqueT ca cb (.at v) (.at v) .keep 5 = [4] := by decide

def chainT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 4) (.node (.leaf 5) (.leaf 6))))
def chainS : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.node (.leaf 1) (.node (.leaf 3) (.leaf 5))) (.node (.leaf 4) (.leaf 6)))
def ba : List Nat := [0,2]
def bb : List Nat := [1,3,5]
def bc : List Nat := [4,6]

theorem chain_labels : ∀ x, x ∈ leaves chainS → x ∈ leaves chainT := by
  intro x hx; simpa [chainS,chainT,leaves,or_assoc,or_comm,or_left_comm] using hx

theorem chain_joint_three : (jointColors bb chainT v w).length = 3 := by decide

theorem chain_original_cover :
    BranchSolution chainT chainS ba bb bc (singles chainS) 6 .keep (.at v) (.at w) ∨
    BranchSolution chainT chainS ba bb bc (singles chainS) 6 .keep (.both v w) .keep ∨
    BranchSolution chainT chainS ba bb bc (singles chainS) 6 (.at v) .keep (.at w) ∨
    BranchSolution chainT chainS ba bb bc (singles chainS) 6 (.at v) (.at w) .keep := by
  apply chain_actual_four_cover chainT chainS ba bb bc (singles chainS) v w 6
    (by decide) (by decide) chain_labels (by decide) (by decide)
  · intro x hx hy; simp [ba,bb] at *; omega
  · intro x hx hy; simp [ba,bc] at *; omega
  · intro x hx hy; simp [bb,bc] at *; omega
  · exact singles_refine chainS ba bb bc (by decide)
  · simp [chainT,v,selectedLeaves,Join]
  · simp [chainT,w,selectedLeaves,Join]
  · decide

def diagT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.node (.leaf 4) (.node (.leaf 5) (.leaf 6))))
def diagS : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.node (.leaf 1) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))
def da : List Nat := [0,2]
def db : List Nat := [1,5]
def dc : List Nat := [4,6]

theorem diag_labels : ∀ x, x ∈ leaves diagS → x ∈ leaves diagT := by
  intro x hx; simpa [diagS,diagT,leaves,or_assoc,or_comm,or_left_comm] using hx

theorem diag_joint_two : (jointColors db diagT v w).length = 2 := by decide

theorem diag_original_cover :
    BranchSolution diagT diagS da db dc (singles diagS) 5 .keep (.both v w) .keep ∨
    BranchSolution diagT diagS da db dc (singles diagS) 5 (.at v) .keep (.at w) := by
  apply chain_actual_diagonal_cover diagT diagS da db dc (singles diagS) v w 5
    (by decide) (by decide) diag_labels (by decide) (by decide)
  · intro x hx hy; simp [da,db] at *; omega
  · intro x hx hy; simp [da,dc] at *; omega
  · intro x hx hy; simp [db,dc] at *; omega
  · exact singles_refine diagS da db dc (by decide)
  · simp [diagT,v,selectedLeaves,Join]
  · simp [diagT,w,selectedLeaves,Join]
  · decide
  · decide
  · exact diag_joint_two
  · decide

theorem diag_literal_costs :
    literalCosts diagS diagT da db .keep (.both v w) .keep 5 = [3] ∧
    literalCosts diagS diagT da db (.at v) .keep (.at w) 5 = [4] := by decide

def refinesBool (xs ys : List (List Nat)) : Bool :=
  xs.all fun b => ys.any fun c => b.all c.contains

theorem original_refinement_direction :
    refinesBool [[0],[1]] [[0,1]] = true ∧ refinesBool [[0,1]] [[0],[1]] = false := by decide

theorem zero_budget_counted :
    (generate cliqueS (requestedColor cliqueT ca cb .keep (.at v) (.at v)) 0).outputs = [] ∧
    (generate cliqueS (requestedColor cliqueT ca cb .keep (.at v) (.at v)) 0).pruned > 0 := by decide

theorem root_two_original_regions : (regions [0,1,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) []).length = 2 := by decide
end Universal233.Assembly.Controls
