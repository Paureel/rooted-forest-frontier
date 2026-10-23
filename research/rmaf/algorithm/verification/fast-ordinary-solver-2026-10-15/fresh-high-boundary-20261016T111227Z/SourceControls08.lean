-- Fresh own exact source-boundary controls, frozen in SOURCE-CONTROLS-PIN-v1.
import SourceBasics05
open RMAF Universal233 OwnHigh SourceBoundary
namespace NewControls
def C := Tree.node (.leaf 0) (.leaf 1)
def S1 := Tree.node (.node (.leaf 0) (.leaf 2)) (.leaf 1)
def S2 := Tree.node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 3)) (.leaf 1)
def S3 := Tree.node (.node (.leaf 0) (.node (.leaf 2) (.leaf 3))) (.leaf 1)
def Sup := Tree.node S1 (.leaf 3)
def T := Tree.node C (.leaf 2)
def ground (S : Tree) (F : List (List Nat)) (P : List Nat) : Bool :=
  decide (leaves S).Nodup && partitionCheck (leaves S) F && pairwiseEmbeddings S F &&
    decide (P ∈ F) && P.contains 0 && P.contains 1
def refines (F Q : List (List Nat)) : Bool := F.all fun P => Q.any fun R => P.all fun x => R.contains x
theorem ground_values :
    ground C [[0,1]] [0,1] = true ∧
    ground S1 [[0,1],[2]] [0,1] = true ∧
    ground S2 [[0,1],[2],[3]] [0,1] = true ∧
    ground S3 [[0,1],[2,3]] [0,1] = true ∧
    ground Sup [[0,1,3],[2]] [0,1,3] = true := by decide
theorem restriction_values :
    restrict [0,1] C = some C ∧ restrict [0,1] S1 = some C ∧
    restrict [0,1] S2 = some C ∧ restrict [0,1] S3 = some C ∧
    restrict [0,1,3] Sup = some (.node C (.leaf 3)) := by decide
theorem cherry_values : HasCherry C 0 1 ∧ HasCherry (.node C (.leaf 3)) 0 1 := by
  exact ⟨⟨[],Or.inl rfl⟩,⟨[false],Or.inl rfl⟩⟩
theorem partition_values :
    CherryBranching.pendantPartition C 0 1 = [[0,1]] ∧
    CherryBranching.pendantPartition S1 0 1 = [[2],[0,1]] ∧
    CherryBranching.pendantPartition S2 0 1 = [[2],[3],[0,1]] ∧
    (CherryBranching.cuts S2 0 1).length = 2 ∧
    CherryBranching.pendantPartition S3 0 1 = [[2,3],[0,1]] ∧
    CherryBranching.pendantPartition Sup 0 1 = [[2],[0,1,3]] := by decide
theorem no_cross_values :
    NoPendantCrossing C 0 1 [[0,1]] ∧ NoPendantCrossing S1 0 1 [[0,1],[2]] ∧
    NoPendantCrossing S2 0 1 [[0,1],[2],[3]] ∧ NoPendantCrossing S3 0 1 [[0,1],[2,3]] ∧
    NoPendantCrossing Sup 0 1 [[0,1,3],[2]] := by
  simp [NoPendantCrossing,CherryBranching.cuts,HardParent.pendantOriginal,
    HardParent.vertices,minimalVertices,rootedSpan,prependSide,HardParent.subtreeLabels,
    C,S1,S2,S3,Sup,leaves]
theorem missing_cherry_ground : partitionCheck (leaves S1) [[0,1,2]] = true ∧
    pairwiseEmbeddings S1 [[0,1,2]] = true ∧ restrict [0,1,2] S1 = some S1 := by decide
theorem missing_cherry_false : ¬ HasCherry S1 0 1 := by
  intro hc
  rcases (node_cherry_iff (.node (.leaf 0) (.leaf 2)) (.leaf 1) 0 1).mp hc with hr | hl | hr
  · simp at hr
  · have h := (has_cherry_labels _ 0 1 hl).2
    simpa [leaves] using h
  · exact leaf_no_cherry 1 0 1 hr
theorem missing_cherry_crosses : ¬ NoPendantCrossing S1 0 1 [[0,1,2]] := by
  intro h
  have hx := h [false,true] (by decide) [0,1,2] (by decide) 2 (by decide) (by decide) 0 (by decide)
  simpa [HardParent.subtreeLabels,S1,leaves] using hx
theorem missing_embedding_ground : partitionCheck (leaves S2) [[0,1],[2,3]] = true ∧
    pairwiseEmbeddings S2 [[0,1],[2,3]] = false := by decide
theorem missing_embedding_crosses : ¬ NoPendantCrossing S2 0 1 [[0,1],[2,3]] := by
  intro h
  have hx := h [false,false,true] (by decide) [2,3] (by decide) 2 (by decide) (by decide) 3 (by decide)
  simpa [HardParent.subtreeLabels,S2,leaves] using hx
theorem corrupt_values :
    refines [[0,1],[2]] [[0],[1],[2]] = false ∧
    CherryBranching.pendantPartition T 0 1 = [[0,1,2]] ∧
    agreement T S1 [[0],[1,2]] = true ∧ agreement T S1 [[1],[0,2]] = true ∧
    refines [[0],[1,2]] [[2],[0,1]] = false ∧ refines [[1],[0,2]] [[2],[0,1]] = false ∧
    ¬ (leaves (.node (.leaf 0) (.leaf 0))).Nodup ∧
    ¬ (leaves (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 0) (.leaf 1)))).Nodup := by decide
theorem equal_literal : CoreGraph.CherryAt (.node (.leaf 0) (.leaf 0)) [] 0 0 := rfl
end NewControls
