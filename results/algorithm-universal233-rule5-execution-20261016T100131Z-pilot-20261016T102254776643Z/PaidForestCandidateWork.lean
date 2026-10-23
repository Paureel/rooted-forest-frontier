import PaidForestPretest
namespace Universal233.Rule5ExecutionSource
open RMAF ForestState CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence

theorem source_leaves_work (ss : List Tree) (N : Nat) (sn : sourceNodes ss≤N) :
 (meterSourceLeaves ss).work≤13*(N+1)^2 := by
 have raw:=meterSourceLeaves_bound ss N sn
 have count:=source_count_nodes ss
 have scaled:=Nat.mul_le_mul_left (8*(N+1)) (Nat.le_trans sn (Nat.le_succ N))
 have p:=pow_mono N 1 2 (by decide)
 simp only [Nat.pow_one,Nat.pow_two,Nat.mul_assoc,Nat.succ_eq_add_one] at raw scaled p ⊢
 omega

def oneCutsCoefficient (N : Nat) :=4096*(N+1)^4

theorem one_cuts_work_rows (ss : List Tree) (N : Nat) (sn : sourceNodes ss≤N) :
 (oneCutsMeter ss).work≤oneCutsCoefficient N*(ss.length+1) := by
 induction ss with
 | nil=>
  have pos:=Nat.one_le_pow 4 (N+1) (by omega)
  simp only [oneCutsMeter,List.length_nil,Nat.zero_add,Nat.mul_one,oneCutsCoefficient]
  omega
 | cons s ss ih=>
  have sN : treeNodes s≤N := Nat.le_trans (source_node_member (s::ss) s (by simp)) sn
  have tailN : sourceNodes ss≤N := by simp only [sourceNodes,List.map_cons,List.sum_cons] at sn ⊢;omega
  have tail:=ih tailN
  have count:=Nat.le_trans (one_cuts_count ss) tailN
  have edgeCount : (meterEdges s).value.length≤N := by
   simp only [meterEdges_value,edges_length];omega
  have pow2:=pow_mono N 2 3 (by decide)
  have pos2:=Nat.one_le_pow 2 (N+1) (by omega)
  have pos3:=Nat.one_le_pow 3 (N+1) (by omega)
  have vertices:=meterVertices_bound s N sN
  have ev:=Nat.mul_le_mul_left (8*(N+1)) (Nat.le_trans sN (Nat.le_succ N))
  have ew : (meterEdges s).work≤12*(N+1)^2 := by
   simp only [meterEdges]
   simp only [Nat.pow_two,Nat.mul_assoc,Nat.succ_eq_add_one] at vertices ev ⊢;omega
  have unchanged:=source_leaves_work ss N tailN
  have leftPoint (p : RMAF.Vertex) (hp : p∈(meterEdges s).value) :
   (let f:=meterForest s (some p);let u:=meterSourceLeaves ss
    (⟨f.value++u.value,f.work+u.work+f.value.length+2⟩:Charged Forest)).work≤150*(N+1)^3 := by
    have candidate : some p∈DepthOne.candidates s := by
     simp only [meterEdges_value] at hp
     simp [DepthOne.candidates,hp]
    have fm:=meterForest_bound s (some p) N sN
     (fun v hv=>Nat.le_trans (candidate_address s (some p) candidate v hv) sN)
    have fc:=forest_cells s (some p)
    simp only [meterForest_value]
    omega
  have left:=meterMap_bound (fun p=>let f:=meterForest s (some p);let u:=meterSourceLeaves ss
   ⟨f.value++u.value,f.work+u.work+f.value.length+2⟩) (meterEdges s).value (150*(N+1)^3) leftPoint
  have lcoeff : 150*(N+1)^3+4≤154*(N+1)^3 := by omega
  have lscale:=Nat.mul_le_mul lcoeff (Nat.add_le_add_right edgeCount 1)
  have leftCap : (meterMap (fun p=>let f:=meterForest s (some p);let u:=meterSourceLeaves ss
   ⟨f.value++u.value,f.work+u.work+f.value.length+2⟩) (meterEdges s).value).work≤154*(N+1)^4 := by
    have scaled : (150*(N+1)^3+4)*((meterEdges s).value.length+1)≤154*(N+1)^4 := by
     simpa only [show 4=3+1 from rfl,Nat.pow_succ,Nat.mul_assoc] using lscale
    exact Nat.le_trans left scaled
  have leaves:=meterLeaves_cap s N sN
  have right:=meterMap_bound (fun F : Forest=>let l:=meterLeaves s;⟨l.value::F,l.work+2⟩) (oneCutsMeter ss).value
   (10*(N+1)^2) (by intro F _;dsimp only;omega)
  have rcoeff : 10*(N+1)^2+4≤14*(N+1)^2:=by omega
  have rscale:=Nat.mul_le_mul rcoeff (Nat.add_le_add_right count 1)
  have rightCap : (meterMap (fun F : Forest=>let l:=meterLeaves s;⟨l.value::F,l.work+2⟩) (oneCutsMeter ss).value).work≤14*(N+1)^3 := by
   have scaled : (10*(N+1)^2+4)*((oneCutsMeter ss).value.length+1)≤14*(N+1)^3 := by
    simpa only [show 3=2+1 from rfl,Nat.pow_succ,Nat.mul_assoc] using rscale
   exact Nat.le_trans right scaled
  have p2:=pow_mono N 2 4 (by decide)
  have p3:=pow_mono N 3 4 (by decide)
  have p1:=pow_mono N 1 4 (by decide)
  have pos4:=Nat.one_le_pow 4 (N+1) (by omega)
  have overhead : (meterEdges s).work+
   (meterMap (fun p=>let f:=meterForest s (some p);let u:=meterSourceLeaves ss
    ⟨f.value++u.value,f.work+u.work+f.value.length+2⟩) (meterEdges s).value).work+
   (meterMap (fun F : Forest=>let l:=meterLeaves s;⟨l.value::F,l.work+2⟩) (oneCutsMeter ss).value).work+
   (meterEdges s).value.length+3≤oneCutsCoefficient N := by
    unfold oneCutsCoefficient
    simp only [Nat.pow_one] at p1
    omega
  dsimp only at overhead
  simp only [oneCutsMeter,meterMap_value,List.length_map,List.length_cons]
  have slot : oneCutsCoefficient N*(ss.length+1+1)=oneCutsCoefficient N*(ss.length+1)+oneCutsCoefficient N := Nat.mul_succ _ _
  rw [slot]
  omega

theorem forest_candidates_work (ss : List Tree) (N : Nat) (sn : sourceNodes ss≤N) :
 (forestCandidatesMeter ss).work≤8192*(N+1)^5 := by
 have one:=one_cuts_work_rows ss N sn
 have count:=source_count_nodes ss
 have scaled:=Nat.mul_le_mul_left (oneCutsCoefficient N) (Nat.add_le_add_right (Nat.le_trans count sn) 1)
 have oneCap : (oneCutsMeter ss).work≤4096*(N+1)^5 := by
  have h : oneCutsCoefficient N*(N+1)=4096*(N+1)^5 := by simp only [oneCutsCoefficient,show 5=4+1 from rfl,Nat.pow_succ,Nat.mul_assoc]
  rw [h] at scaled;omega
 have unchanged:=source_leaves_work ss N sn
 have lift:=pow_mono N 2 5 (by decide)
 have pos:=Nat.one_le_pow 5 (N+1) (by omega)
 simp only [forestCandidatesMeter]
 omega
end Universal233.Rule5ExecutionSource
