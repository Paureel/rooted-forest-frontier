import ForestPretestSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork

theorem oneCutsForest_count (ss : List Tree) : (ForestPretest01.oneCuts ss).length≤sourceNodes ss:=by
 induction ss with
 | nil=>simp [ForestPretest01.oneCuts,sourceNodes]
 | cons s ss ih=>
   simp only [ForestPretest01.oneCuts,List.length_append,List.length_map,edges_length,
    sourceNodes,List.map_cons,List.sum_cons] at *
   omega

theorem oneCutsForest_cells (ss : List Tree) (F : Forest) (mem:F∈ForestPretest01.oneCuts ss) :
 F.flatten.length≤2*sourceNodes ss:=by
 induction ss generalizing F with
 | nil=>simp [ForestPretest01.oneCuts] at mem
 | cons s ss ih=>
   simp only [ForestPretest01.oneCuts,List.mem_append,List.mem_map] at mem
   rcases mem with ⟨p,hp,rfl⟩|⟨G,hg,rfl⟩
   · have f:=(forest_cells s (some p)).2
     have t:=source_leaves_cells ss
     simp only [List.flatten_append,List.length_append,ForestPretest01.unchanged,
      sourceNodes,List.map_cons,List.sum_cons] at *
     omega
   · have t:=ih G hg
     have l:=leaves_nodes s
     simp only [List.flatten_cons,List.length_append,sourceNodes,List.map_cons,List.sum_cons] at *
     omega

theorem pretestCandidate_payload (ss : List Tree) (F : Forest) (mem:F∈ForestPretest01.candidates ss) :
 F.length≤ss.length+1 ∧ F.flatten.length≤2*sourceNodes ss:=by
 rcases List.mem_cons.1 mem with eq|hm
 · subst F
   have c:=source_leaves_cells ss
   simp only [ForestPretest01.unchanged,List.length_map];omega
 · have l:=ForestPretest01.oneCuts_length ss F hm
   exact ⟨by omega,oneCutsForest_cells ss F hm⟩
end OrdinaryDispatch.Hard2SourceWork
