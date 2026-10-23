import KeptConsumers

namespace Universal233.KeptParent.Controls
open RMAF CoreProgram CutRealization

def S : Tree := .node (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3))
  (.node (.node (.leaf 4) (.leaf 6)) (.node (.leaf 5) (.leaf 7)))
def wholeS : Tree := .node S (.leaf 8)
def T : Tree := .node (.node (.leaf 1) (.node (.leaf 2) (.leaf 3)))
  (.node (.node (.leaf 4) (.leaf 5)) (.node (.leaf 6) (.leaf 7)))
def wholeT : Tree := .node T (.leaf 8)
def A : List Nat := [1,2,3]
def B : List Nat := [4,5,6,7]
def C : List Nat := [8]
def cb (x : Nat) : Nat := if x < 6 then 0 else 1

theorem proper : partitionCheck (leaves wholeS) [A,B,C] = true := by decide
theorem original_embeddings : pairwiseEmbeddings wholeS [A,B,C] = true := by decide
theorem exact_tags : keepColor A B cb 1 = 0 ∧ keepColor A B cb 4 = 1 ∧
    keepColor A B cb 6 = 4 ∧ keepColor A B cb 8 = 2 := by decide
theorem q0 : (generate wholeS (keepColor A B cb) 0).outputs = [] := by decide
theorem repeated_refusal : (generate (.node (.leaf 1) (.leaf 1)) id 3).refusals =
    ["duplicate original label"] := by decide
theorem repeated_partition_rejected : partitionCheck [1,1] [[1,1]] = false := by decide

theorem universal_instance (q : Nat) (o : Output)
    (ho : o ∈ (generate wholeS (keepColor A B cb) q).outputs) : Keeps A o ∧ Keeps C o :=
  generated_keeps_A_C wholeS A B C cb proper original_embeddings q o ho

def localS : Tree := .node (.node (.leaf 1) (.leaf 2)) (.leaf 3)
def localT : Tree := .node (.leaf 1) (.node (.leaf 2) (.leaf 3))
def localColor (x : Nat) : Nat := if x = 1 then 0 else 1
def localOne : Output := ⟨[[1],[2,3]], [[false,false]]⟩
theorem local_literal : localOne ∈ (generate localS localColor 1).outputs := by decide
theorem supplied_actual_local_cut : OriginalLocalOneCut wholeS wholeT A localOne := by
  refine ⟨localS,localT,by decide,by decide,?_,by decide,by decide⟩
  exact generate_original_realization localS localColor 1 localOne local_literal

theorem original_A_bad : restrictionAgrees wholeS wholeT A = false := by decide
theorem every_output_paid (q : Nat) (o : Output)
    (ho : o ∈ (generate wholeS (keepColor A B cb) q).outputs) :
    ∃ K, K ∈ o.partition ∧ SameMembers K A ∧ OriginalLocalOneCut wholeS wholeT K localOne :=
  every_output_retains_original_local_cut wholeS wholeT A B C cb proper original_embeddings
    localOne supplied_actual_local_cut q o ho

def badS : Tree := .node (.node (.node (.node (.node (.leaf 1)
  (.node (.leaf 4) (.leaf 6))) (.node (.leaf 5) (.leaf 7))) (.leaf 2)) (.leaf 3)) (.leaf 8)
def badCB (x : Nat) : Nat := if x = 4 ∨ x = 5 then 0 else 1

def hasMembers (a : List Nat) (o : Output) : Bool :=
  o.partition.any (fun b => b.all a.contains && a.all b.contains)

theorem overlap_partition_only : partitionCheck (leaves badS) [A,B,C] = true := by decide
theorem overlap_guard_rejected : pairwiseEmbeddings badS [A,B,C] = false := by decide
theorem overlap_A_split_two : ((generate badS (keepColor A B badCB) 7).outputs.filter
    (fun o => !(hasMembers A o))).length = 2 := by decide

theorem clean_twin : hasMembers A ⟨[[1,2,3],[4],[5],[6],[7],[8]],[]⟩ = true := by decide
theorem corruption_caught : hasMembers A ⟨[[1,2],[4],[5],[6],[7],[8]],[]⟩ = false := by decide

end Universal233.KeptParent.Controls
