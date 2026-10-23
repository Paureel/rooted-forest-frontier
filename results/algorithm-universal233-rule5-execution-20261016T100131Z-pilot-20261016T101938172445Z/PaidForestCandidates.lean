import CommonCallBinding
import CheckBounds
namespace Universal233.Rule5ExecutionSource
open RMAF ForestState CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence

/-- Preserve the repeated unchanged-tail construction inside every left map,
and the repeated leaves extraction inside every right map. -/
def oneCutsMeter : List Tree→Charged (List Forest)
 | []=>⟨[],1⟩
 | s::ss=>
   let es:=meterEdges s
   let left:=meterMap (fun p=>let f:=meterForest s (some p);let u:=meterSourceLeaves ss
    ⟨f.value++u.value,f.work+u.work+f.value.length+2⟩) es.value
   let tail:=oneCutsMeter ss
   let right:=meterMap (fun F=>let l:=meterLeaves s;⟨l.value::F,l.work+2⟩) tail.value
   ⟨left.value++right.value,es.work+left.work+tail.work+right.work+left.value.length+3⟩

theorem one_cuts_value (ss : List Tree) : (oneCutsMeter ss).value=ForestPretest01.oneCuts ss := by
 induction ss with
 | nil=>rfl
 | cons s ss ih=>
  simp only [oneCutsMeter,meterMap_value,meterEdges_value,meterForest_value,meterSourceLeaves_value,meterLeaves_value,ih,ForestPretest01.oneCuts,ForestPretest01.unchanged]

theorem source_count_nodes (ss : List Tree) : ss.length≤sourceNodes ss := by
 induction ss with
 | nil=>simp [sourceNodes]
 | cons s ss ih=>have pos:=treeNodes_pos s;simp only [List.length_cons,sourceNodes,List.map_cons,List.sum_cons];omega

theorem one_cuts_count (ss : List Tree) : (oneCutsMeter ss).value.length≤sourceNodes ss := by
 rw [one_cuts_value]
 induction ss with
 | nil=>simp [ForestPretest01.oneCuts,sourceNodes]
 | cons s ss ih=>
  have es:=edges_length s
  simp only [ForestPretest01.oneCuts,List.length_append,List.length_map,sourceNodes,List.map_cons,List.sum_cons]
  omega

theorem one_cuts_payload (ss : List Tree) {F : Forest} (mem : F∈(oneCutsMeter ss).value) :
 F.length≤ss.length+1 ∧ F.flatten.length≤2*sourceNodes ss := by
 rw [one_cuts_value] at mem
 induction ss generalizing F with
 | nil=>simp [ForestPretest01.oneCuts] at mem
 | cons s ss ih=>
  simp only [ForestPretest01.oneCuts,List.mem_append,List.mem_map] at mem
  rcases mem with ⟨p,hp,rfl⟩|⟨G,hG,rfl⟩
  · have f:=forest_cells s (some p)
    have u:=source_leaves_cells ss
    simp only [ForestPretest01.unchanged,List.length_append,List.length_map,List.flatten_append,List.length_cons,sourceNodes,List.map_cons,List.sum_cons]
    omega
  · have tail:=ih hG
    have l:=leaves_nodes s
    simp only [List.length_cons,List.flatten_cons,List.length_append,sourceNodes,List.map_cons,List.sum_cons]
    omega

def forestCandidatesMeter (ss : List Tree) : Charged (List Forest) :=
 let unchanged:=meterSourceLeaves ss;let one:=oneCutsMeter ss
 ⟨unchanged.value::one.value,unchanged.work+one.work+2⟩

theorem forest_candidates_value (ss : List Tree) :
 (forestCandidatesMeter ss).value=ForestPretest01.candidates ss := by
 simp only [forestCandidatesMeter,meterSourceLeaves_value,one_cuts_value,ForestPretest01.candidates,ForestPretest01.unchanged]

theorem forest_candidates_count (ss : List Tree) :
 (forestCandidatesMeter ss).value.length≤sourceNodes ss+1 := by
 have h:=one_cuts_count ss;simp only [forestCandidatesMeter,List.length_cons];omega

theorem forest_candidates_payload (ss : List Tree) {F : Forest} (mem : F∈(forestCandidatesMeter ss).value) :
 F.length≤sourceNodes ss+1 ∧ F.flatten.length≤2*sourceNodes ss := by
 simp only [forestCandidatesMeter,List.mem_cons] at mem
 have count:=source_count_nodes ss
 rcases mem with rfl|mem
 · have cells:=source_leaves_cells ss
   simp only [meterSourceLeaves_value,List.length_map];omega
 · have h:=one_cuts_payload ss mem;omega
end Universal233.Rule5ExecutionSource
