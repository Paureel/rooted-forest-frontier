import Composition
namespace GeometryFreshControls
open RMAF VertexGeometry
def sameVertices (a b : List VertexGeometry.Vertex) : Bool :=
  a.all b.contains && b.all a.contains
def forestCheck (t : Tree) (ss : List Tree) (F : List (List Nat)) : Bool :=
  partitionCheck (leaves t) (ss.map leaves) && partitionCheck (leaves t) F &&
  pairwiseEmbeddings t F &&
  F.all (fun P =>
    let owners := ss.filter (fun s => P.all (leaves s).contains)
    owners.length == 1 && match owners.head? with
      | none => false
      | some s => restrictionAgrees t s P) &&
  ss.all (fun s => pairwiseEmbeddings s (F.filter (fun P => P.all (leaves s).contains)))
theorem control_001 : sameVertices (minimalVertices [0] (.leaf 0)) [[]] = true := by decide +kernel

theorem control_002 : sameVertices (minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))) [] = true := by decide +kernel

theorem control_003 : sameVertices (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))) [[true,false]] = true := by decide +kernel

theorem control_004 : sameVertices (minimalVertices [1,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))) [[true],[true,false],[true,true]] = true := by decide +kernel

theorem control_005 : sameVertices (minimalVertices [0,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))) [[],[false],[true],[true,true]] = true := by decide +kernel

theorem control_006 : sameVertices (minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1))))) [[],[false],[true],[true,true],[true,true,true]] = true := by decide +kernel

theorem control_007 : findCommon (minimalVertices [0,2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 4) (.leaf 5))))) (minimalVertices [1,4] (.node (.node (.leaf 0) (.leaf 1)) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 4) (.leaf 5))))) (minimalVertices [3,5] (.node (.node (.leaf 0) (.leaf 1)) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 4) (.leaf 5))))) = some [true] := by decide +kernel

theorem control_008 : findCommon (minimalVertices [0,2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))) (minimalVertices [0,3] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))) (minimalVertices [1,2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))) = some [] := by decide +kernel

theorem control_009 : findCommon (minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))) (minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))) (minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))) = none := by decide +kernel

theorem control_010 : (regions [0,1,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) []).length = 2 := by decide +kernel

theorem control_011 : ([[]].all (fun v => !(minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = true := by decide +kernel

theorem control_012 : ([[]].all (fun v => !(minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = true := by decide +kernel

theorem control_013 : ([[]].all (fun v => !(minimalVertices [2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = true := by decide +kernel

theorem control_014 : ([[]].all (fun v => !(minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = false := by decide +kernel

theorem control_015 : ([[]].all (fun v => !(minimalVertices [0,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = false := by decide +kernel

theorem control_016 : ([[]].all (fun v => !(minimalVertices [1,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = true := by decide +kernel

theorem control_017 : ([[]].all (fun v => !(minimalVertices [0,1,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = false := by decide +kernel

theorem control_018 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 0) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 0)) = true := by decide +kernel

theorem control_019 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 0) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 1)) = false := by decide +kernel

theorem control_020 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 0) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 2)) = false := by decide +kernel

theorem control_021 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 1) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 1)) = true := by decide +kernel

theorem control_022 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 1) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 2)) = true := by decide +kernel

theorem control_023 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 2) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 2)) = true := by decide +kernel

theorem control_024 : (regions [0,1,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true]).length = 3 := by decide +kernel

theorem control_025 : ([[true]].all (fun v => !(minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = true := by decide +kernel

theorem control_026 : ([[true]].all (fun v => !(minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = true := by decide +kernel

theorem control_027 : ([[true]].all (fun v => !(minimalVertices [2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = true := by decide +kernel

theorem control_028 : ([[true]].all (fun v => !(minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = false := by decide +kernel

theorem control_029 : ([[true]].all (fun v => !(minimalVertices [0,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = false := by decide +kernel

theorem control_030 : ([[true]].all (fun v => !(minimalVertices [1,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = false := by decide +kernel

theorem control_031 : ([[true]].all (fun v => !(minimalVertices [0,1,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))).contains v)) = false := by decide +kernel

theorem control_032 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true] 0) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true] 0)) = true := by decide +kernel

theorem control_033 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true] 0) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true] 1)) = false := by decide +kernel

theorem control_034 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true] 0) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true] 2)) = false := by decide +kernel

theorem control_035 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true] 1) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true] 1)) = true := by decide +kernel

theorem control_036 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true] 1) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true] 2)) = false := by decide +kernel

theorem control_037 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true] 2) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [true] 2)) = true := by decide +kernel

theorem control_038 : (regions [1,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) []).length = 1 := by decide +kernel

theorem control_039 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 1) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 1)) = true := by decide +kernel

theorem control_040 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 1) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 2)) = true := by decide +kernel

theorem control_041 : ((colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 2) == (colorLabel (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [] 2)) = true := by decide +kernel

theorem control_042 : (regions [0,1,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [false]).length = 1 := by decide +kernel

theorem control_043 : (jointColors [0,1] (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] [true,true]).length = 2 := by decide +kernel

theorem control_044 : ([[],[true,true]].all (fun v => !(minimalVertices [0] (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1))))).contains v)) = true := by decide +kernel

theorem control_045 : ([[],[true,true]].all (fun v => !(minimalVertices [1] (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1))))).contains v)) = true := by decide +kernel

theorem control_046 : ([[],[true,true]].all (fun v => !(minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1))))).contains v)) = false := by decide +kernel

theorem control_047 : ((colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 0, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 0) == (colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 0, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 0)) = true := by decide +kernel

theorem control_048 : ((colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 0, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 0) == (colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 1, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 1)) = false := by decide +kernel

theorem control_049 : ((colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 1, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 1) == (colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 1, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 1)) = true := by decide +kernel

theorem control_050 : (jointColors [0,8,1] (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] [true,true]).length = 3 := by decide +kernel

theorem control_051 : ((colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 0, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 0) == (colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 0, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 0)) = true := by decide +kernel

theorem control_052 : ((colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 0, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 0) == (colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 1, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 1)) = false := by decide +kernel

theorem control_053 : ((colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 0, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 0) == (colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 8, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 8)) = false := by decide +kernel

theorem control_054 : ((colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 1, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 1) == (colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 1, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 1)) = true := by decide +kernel

theorem control_055 : ((colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 1, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 1) == (colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 8, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 8)) = false := by decide +kernel

theorem control_056 : ((colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 8, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 8) == (colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [] 8, colorLabel (.node (.leaf 0) (.node (.leaf 8) (.node (.leaf 9) (.leaf 1)))) [true,true] 8)) = true := by decide +kernel

theorem control_057 : (jointColors [0,1] (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10))))) [] [true,true,true]).length = 2 := by decide +kernel

theorem control_058 : (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10)))))).contains [] = (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10)))))).contains [true,true,true] := by decide +kernel

theorem control_059 : (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10)))))).contains [] = (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10)))))).contains [true,true,true] := by decide +kernel

theorem control_060 : (minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10)))))).contains [] = (minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10)))))).contains [true,true,true] := by decide +kernel

theorem control_061 : (jointColors [0,6,1] (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 6) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10)))))) [] [true,true,true,true]).length = 3 := by decide +kernel

theorem control_062 : (minimalVertices [0,6] (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 6) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10))))))).contains [] = true ∧ (minimalVertices [0,6] (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 6) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10))))))).contains [true,true,true,true] = false := by decide +kernel

theorem control_063 : forestCheck (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [(.node (.leaf 0) (.leaf 1)),(.node (.leaf 2) (.leaf 3))] [[0,1],[2,3]] = true := by decide +kernel

theorem control_064 : forestCheck (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [(.node (.leaf 0) (.leaf 2)),(.node (.leaf 1) (.leaf 3))] [[0,2],[1,3]] = false := by decide +kernel

theorem control_065 : forestCheck (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [(.node (.leaf 0) (.leaf 1)),(.node (.leaf 2) (.leaf 3))] [[0,2],[1,3]] = false := by decide +kernel

theorem control_066 : forestCheck (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [(.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3)))] [[0,1,2,3]] = false := by decide +kernel

theorem control_067 : forestCheck (.leaf 0) [(.leaf 0)] [[0]] = true := by decide +kernel

theorem control_068 : forestCheck (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10))))) [(.node (.leaf 7) (.leaf 8)),(.node (.leaf 0) (.leaf 1)),(.node (.leaf 9) (.leaf 10))] [[7,8],[0],[1],[9,10]] = true := by decide +kernel

theorem control_069 : forestCheck (.node (.node (.leaf 0) (.leaf 7)) (.node (.leaf 8) (.node (.leaf 9) (.node (.leaf 1) (.leaf 10))))) [(.node (.leaf 7) (.leaf 8)),(.node (.leaf 0) (.leaf 1)),(.node (.leaf 9) (.leaf 10))] [[7],[8],[0,1],[9],[10]] = true := by decide +kernel

end GeometryFreshControls
