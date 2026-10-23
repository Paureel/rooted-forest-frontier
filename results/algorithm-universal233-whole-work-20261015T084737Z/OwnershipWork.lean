import ColorWork

namespace Universal233.WholeSourceWork
open RMAF VertexGeometry CoreProgram CoreWork WholeSourceMass SourceCoverage

structure ColorInitial where
  tree : GTree
  calls : Nat
  work : Nat
  deriving Repr

/-- Color part of the actual conversion: exactly one concrete callback per leaf.
All non-color fromTree/address work remains in frozen initialCharge. -/
def meterColorTree (T : Tree) (A B : List Nat) (c : Colors)
    (p : RMAF.Vertex) : Tree → ColorInitial
  | .leaf x =>
    let r := meterTagged T A B c x
    ⟨.leaf ⟨p,[x],r.value⟩,1,r.work⟩
  | .node l r =>
    let a := meterColorTree T A B c (p++[false]) l
    let b := meterColorTree T A B c (p++[true]) r
    ⟨.node p a.tree b.tree,a.calls+b.calls,a.work+b.work⟩

@[simp] theorem meterColorTree_value (T A B c p S) :
    (meterColorTree T A B c p S).tree = fromTree (colors T A B c) p S := by
  induction S generalizing p with
  | leaf x => simp [meterColorTree,fromTree]
  | node l r ihl ihr => simp [meterColorTree,fromTree,ihl,ihr]

@[simp] theorem meterColorTree_calls (T A B c p S) :
    (meterColorTree T A B c p S).calls = (leaves S).length := by
  induction S generalizing p with
  | leaf x => rfl
  | node l r ihl ihr => simp [meterColorTree,leaves,ihl,ihr]

theorem meterColorTree_work (T A B c p S) :
    (meterColorTree T A B c p S).work =
      ((leaves S).map (fun x => (meterTagged T A B c x).work)).sum := by
  induction S generalizing p with
  | leaf x => simp [meterColorTree,leaves]
  | node l r ihl ihr => simp [meterColorTree,leaves,ihl,ihr,List.map_append,List.sum_append]

theorem meterColorTree_bound (T A B c p S) :
    (meterColorTree T A B c p S).work ≤ taggedCap T A B c*(leaves S).length := by
  induction S generalizing p with
  | leaf x => simpa [meterColorTree,leaves] using meterTagged_bound T A B c x
  | node l r ihl ihr =>
    have hl := ihl (p++[false])
    have hr := ihr (p++[true])
    simp only [meterColorTree,leaves,List.length_append,Nat.mul_add]
    omega

def budgetCap (S : Tree) (q : Nat) : Nat := min q ((leaves S).length-1)
def coreBound (S : Tree) (q : Nat) : Nat := initialCharge S+
  (cap (inputResource S)+6)*(budgetCap S q+1)*2^(budgetCap S q+1)
def recordBound (S : Tree) (q : Nat) : Nat := 3*2^(budgetCap S q+1)
def wholeBound (S T : Tree) (A B : List Nat) (c : Colors) (q : Nat) : Nat :=
  coreBound S q+taggedCap T A B c*(leaves S).length

structure Owned where
  outputs : List Output
  work : Nat
  copied : Nat
  colorCalls : Nat
  pruned : Nat
  deriving Repr

def meterWhole (S T : Tree) (A B : List Nat) (c : Colors) (q : Nat) : Owned :=
  let r := meterGenerate S (colors T A B c) q
  let init := if (leaves S).Nodup then meterColorTree T A B c [] S
      else ⟨fromTree (colors T A B c) [] S,0,0⟩
  ⟨r.measured.receipt.outputs,r.measured.work+init.work,r.measured.copied,
    init.calls,r.measured.receipt.pruned⟩

@[simp] theorem meterWhole_outputs (S T A B c q) :
    (meterWhole S T A B c q).outputs = wholeOutputs S A B
      (localColor T c.a) (localColor T c.b) (localColor T c.c) q := by
  simp [meterWhole,meterGenerate_receipt,wholeOutputs,colors]

theorem meterWhole_colorCalls (S T A B c q) :
    (meterWhole S T A B c q).colorCalls =
      if (leaves S).Nodup then (leaves S).length else 0 := by
  unfold meterWhole
  split <;> simp [meterColorTree_calls]

theorem meterWhole_pruned (S T A B c q) :
    (meterWhole S T A B c q).pruned = (generate S (colors T A B c) q).pruned := by
  simp [meterWhole,meterGenerate_receipt]

theorem meterWhole_bound (S T A B c q) :
    (meterWhole S T A B c q).work ≤ wholeBound S T A B c q := by
  have h := generate_work_bound S (colors T A B c) q
  change (meterGenerate S (colors T A B c) q).measured.work ≤ coreBound S q at h
  have hc := meterColorTree_bound T A B c [] S
  dsimp only [meterWhole,wholeBound]
  split <;> (try simp only [ColorInitial.work]) <;> omega

theorem generate_outputs_bound (S : Tree) (color : Nat → Nat) (q : Nat) :
    (generate S color q).outputs.length ≤ recordBound S q := by
  unfold generate
  split
  · have h := run_records_bound (budgetCap S q) (fromTree color [] S) [] []
    unfold records recordBound budgetCap at *
    omega
  · simp [recordBound]

theorem meterWhole_length (S T A B c q) :
    (meterWhole S T A B c q).outputs.length ≤ recordBound S q := by
  simp only [meterWhole_outputs,wholeOutputs]
  exact generate_outputs_bound S _ q

/-- Immutable-list append: actual left output spine is materialized.
The result elements and their inner cut/partition objects remain shared. -/
def appendOwned (a b : Owned) : Owned :=
  ⟨a.outputs++b.outputs,a.work+b.work+a.outputs.length+2,
    a.copied+b.copied+a.outputs.length,a.colorCalls+b.colorCalls,a.pruned+b.pruned⟩

def cliqueColors (v : RMAF.Vertex) : Colors × Colors × Colors :=
  (⟨.keep,.single v,.single v⟩,⟨.single v,.keep,.single v⟩,⟨.single v,.single v,.keep⟩)
def chainColors (v w : RMAF.Vertex) : Colors × Colors × Colors × Colors :=
  (⟨.keep,.single v,.single w⟩,⟨.keep,.joint v w,.keep⟩,
    ⟨.single v,.keep,.single w⟩,⟨.single v,.single w,.keep⟩)

def meterClique (S T : Tree) (A B : List Nat) (v : RMAF.Vertex) (q : Nat) : Owned :=
  let cs := cliqueColors v
  appendOwned (appendOwned (meterWhole S T A B cs.1 q)
    (meterWhole S T A B cs.2.1 q)) (meterWhole S T A B cs.2.2 q)

def meterChain (S T : Tree) (A B : List Nat) (v w : RMAF.Vertex) (q : Nat) : Owned :=
  let cs := chainColors v w
  appendOwned (appendOwned (appendOwned (meterWhole S T A B cs.1 q)
    (meterWhole S T A B cs.2.1 q)) (meterWhole S T A B cs.2.2.1 q))
      (meterWhole S T A B cs.2.2.2 q)

def meterDiagonal (S T : Tree) (A B : List Nat) (v w : RMAF.Vertex) (q : Nat) : Owned :=
  let cs := chainColors v w
  appendOwned (meterWhole S T A B cs.2.1 q) (meterWhole S T A B cs.2.2.1 q)

@[simp] theorem meterClique_outputs (S T A B v q) :
    (meterClique S T A B v q).outputs = cliqueOutputs S T A B v q := by
  simp [meterClique,cliqueColors,appendOwned,cliqueOutputs,localColor]

@[simp] theorem meterChain_outputs (S T A B v w q) :
    (meterChain S T A B v w q).outputs = fourChainOutputs S T A B v w q := by
  simp [meterChain,chainColors,appendOwned,fourChainOutputs,localColor]

@[simp] theorem meterDiagonal_outputs (S T A B v w q) :
    (meterDiagonal S T A B v w q).outputs = diagonalOutputs S T A B v w q := by
  simp [meterDiagonal,chainColors,appendOwned,diagonalOutputs,localColor]

/-- Sum the ACTUAL capped generate bounds and all outer append left spines.
No additional initial hard2 factor or reduced pre-call budget occurs. -/
theorem meterClique_bound (S T A B v q) :
    (meterClique S T A B v q).work ≤
      wholeBound S T A B (cliqueColors v).1 q+
      wholeBound S T A B (cliqueColors v).2.1 q+
      wholeBound S T A B (cliqueColors v).2.2 q+3*recordBound S q+4 := by
  have h1 := meterWhole_bound S T A B (cliqueColors v).1 q
  have h2 := meterWhole_bound S T A B (cliqueColors v).2.1 q
  have h3 := meterWhole_bound S T A B (cliqueColors v).2.2 q
  have l1 := meterWhole_length S T A B (cliqueColors v).1 q
  have l2 := meterWhole_length S T A B (cliqueColors v).2.1 q
  simp only [meterClique,appendOwned,List.length_append]
  omega

theorem meterChain_bound (S T A B v w q) :
    (meterChain S T A B v w q).work ≤
      wholeBound S T A B (chainColors v w).1 q+
      wholeBound S T A B (chainColors v w).2.1 q+
      wholeBound S T A B (chainColors v w).2.2.1 q+
      wholeBound S T A B (chainColors v w).2.2.2 q+6*recordBound S q+6 := by
  have h1 := meterWhole_bound S T A B (chainColors v w).1 q
  have h2 := meterWhole_bound S T A B (chainColors v w).2.1 q
  have h3 := meterWhole_bound S T A B (chainColors v w).2.2.1 q
  have h4 := meterWhole_bound S T A B (chainColors v w).2.2.2 q
  have l1 := meterWhole_length S T A B (chainColors v w).1 q
  have l2 := meterWhole_length S T A B (chainColors v w).2.1 q
  have l3 := meterWhole_length S T A B (chainColors v w).2.2.1 q
  simp only [meterChain,appendOwned,List.length_append]
  omega

theorem meterDiagonal_bound (S T A B v w q) :
    (meterDiagonal S T A B v w q).work ≤
      wholeBound S T A B (chainColors v w).2.1 q+
      wholeBound S T A B (chainColors v w).2.2.1 q+recordBound S q+2 := by
  have h1 := meterWhole_bound S T A B (chainColors v w).2.1 q
  have h2 := meterWhole_bound S T A B (chainColors v w).2.2.1 q
  have l1 := meterWhole_length S T A B (chainColors v w).2.1 q
  simp only [meterDiagonal,appendOwned]
  omega

/-- The shared-call outputs retain the frozen raw mass bounds literally. -/
theorem metered_clique_mass (S T A B C) (h : WholeCall S T A B C) (v)
    (hA : Occupied A T v) (hB : Occupied B T v) (hC : Occupied C T v)
    (q : Nat) (b : Rat) (hb : 2 ≤ b) :
    rawQMass b (meterClique S T A B v q).outputs ≤ 3*b^(-4 : Int) := by
  rw [meterClique_outputs]
  exact clique_raw_mass S T A B C h v hA hB hC q b hb

theorem metered_chain_mass (S T A B C) (h : WholeCall S T A B C) (v w)
    (hA : Occupied A T v) (hBv : Occupied B T v) (hBw : Occupied B T w)
    (hC : Occupied C T w) (hj : 3 ≤ (jointColors B T v w).length)
    (q : Nat) (b : Rat) (hb : 2 ≤ b) :
    rawQMass b (meterChain S T A B v w q).outputs ≤ 4*b^(-4 : Int) := by
  rw [meterChain_outputs]
  exact four_chain_raw_mass S T A B C h v w hA hBv hBw hC hj q b hb

theorem metered_diagonal_mass (S T A B C) (h : WholeCall S T A B C) (v w)
    (hA : Occupied A T v) (hC : Occupied C T w)
    (hj : (jointColors B T v w).length = 2)
    (q : Nat) (b : Rat) (hb : 2 ≤ b) :
    rawQMass b (meterDiagonal S T A B v w q).outputs ≤ b^(-3 : Int)+b^(-4 : Int) := by
  rw [meterDiagonal_outputs]
  exact diagonal_raw_mass S T A B C h v w hA hC hj q b hb

end Universal233.WholeSourceWork
