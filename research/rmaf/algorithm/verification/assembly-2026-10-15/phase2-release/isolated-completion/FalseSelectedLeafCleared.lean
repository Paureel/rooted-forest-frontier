import HardPaid
open RMAF Universal233 CoreProgram SourceCoverage VertexGeometry
def refinesB (F Q : List (List Nat)) : Bool := F.all (fun p => Q.any (fun q => p.all q.contains))
def hardSource : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 3)) (Tree.leaf 1))
def hardTarget : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2)) (Tree.leaf 3))
def S0 : Tree := (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.node (Tree.leaf 2) (Tree.leaf 3)) (Tree.node (Tree.leaf 4) (Tree.leaf 5))))
def T0 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 4)) (Tree.node (Tree.node (Tree.leaf 1) (Tree.leaf 3)) (Tree.leaf 5)))
def os0 (q : Nat) := WholeSourceMass.cliqueOutputs S0 T0 [0, 1] [2, 3] [] q
def S1 : Tree := (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.node (Tree.leaf 2) (Tree.node (Tree.leaf 3) (Tree.leaf 6))) (Tree.node (Tree.leaf 4) (Tree.leaf 5))))
def T1 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 1)) (Tree.node (Tree.leaf 3) (Tree.node (Tree.leaf 4) (Tree.node (Tree.leaf 6) (Tree.leaf 5)))))
def os1 (q : Nat) := WholeSourceMass.fourChainOutputs S1 T1 [0, 1] [2, 3, 6] [false, false] [true, true] q
def S2 : Tree := (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.node (Tree.leaf 2) (Tree.leaf 3)) (Tree.node (Tree.leaf 4) (Tree.leaf 5))))
def T2 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 1)) (Tree.node (Tree.leaf 4) (Tree.node (Tree.leaf 3) (Tree.leaf 5))))
def os2 (q : Nat) := WholeSourceMass.diagonalOutputs S2 T2 [0, 1] [2, 3] [false, false] [true, true] q
def badS : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 6)) (Tree.node (Tree.node (Tree.leaf 2) (Tree.leaf 3)) (Tree.node (Tree.leaf 4) (Tree.leaf 5))))
def badT : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 4)) (Tree.node (Tree.node (Tree.node (Tree.leaf 1) (Tree.leaf 3)) (Tree.leaf 6)) (Tree.leaf 5)))
def badQ : Output := ((generate badS (Assembly.requestedColor badT [0, 1, 6] [2, 3] Assembly.Request.keep (Assembly.Request.at []) (Assembly.Request.at [])) 6).outputs).getD 0 ⟨[],[]⟩
def duplicateClique := os0 4 ++ [(os0 4).getD 0 ⟨[],[]⟩]
theorem trueMass2 : rawQMass 2 (os0 4) = mkRat 3 16 := by decide +kernel
theorem trueMass233 : rawQMass (233/100) (os0 4) = mkRat 300000000 2947295521 := by decide +kernel
theorem trueDuplicateMass2 : rawQMass 2 duplicateClique = mkRat 1 4 := by decide +kernel

example : (minimalVertices [0] (.node (.leaf 0) (.leaf 1))).contains [false] = false := by
  decide
