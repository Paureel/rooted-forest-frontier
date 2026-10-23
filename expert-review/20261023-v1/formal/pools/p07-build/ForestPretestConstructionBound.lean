import ForestPretestPayload
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork

def unchangedForestPolynomial (N : Nat):=(8*(N+1)^2+4)*(N+1)

theorem unchangedForestMeter_bound (ss : List Tree) (N : Nat)
 (sn:sourceNodes ss≤N) (sl:ss.length≤N) :
 (unchangedForestMeter ss).work≤unchangedForestPolynomial N:=by
 have h:=meterMap_bound meterLeaves ss (8*(N+1)^2)
  (by intro s hm;exact meterLeaves_cap s N (Nat.le_trans (source_node_member ss s hm) sn))
 exact Nat.le_trans h (Nat.mul_le_mul_left _ (Nat.add_le_add_right sl 1))

def oneCutStepPolynomial (N : Nat):=
 (8*(N+1)*N+4)+(128*(N+1)^3+unchangedForestPolynomial N+16)*(N+1)+
 (8*(N+1)^2+12)*(N+1)+2*N+12

theorem oneCutsForestMeter_bound (ss : List Tree) (N : Nat)
 (sn:sourceNodes ss≤N) (sl:ss.length≤N) :
 (oneCutsForestMeter ss).work≤oneCutStepPolynomial N*ss.length+2:=by
 induction ss with
 | nil=>simp [oneCutsForestMeter]
 | cons s ss ih=>
   have splitn:treeNodes s+sourceNodes ss≤N:=by
    simpa only [sourceNodes,List.map_cons,List.sum_cons] using sn
   have nodes:treeNodes s≤N:=by omega
   have tails:sourceNodes ss≤N:=by omega
   have lens:ss.length≤N:=by simp only [List.length_cons] at sl;omega
   have tail:=ih tails lens
   have u:=unchangedForestMeter_bound ss N tails lens
   have edge:=meterVertices_bound s N nodes
   have edge':(meterEdges s).work≤8*(N+1)*N+4:=by
    have mul:=Nat.mul_le_mul_left (8*(N+1)) nodes
    simp only [meterEdges];omega
   have elen:(meterEdges s).value.length≤N:=by rw [meterEdges_value,edges_length];omega
   have head:=meterMap_bound (fun p=>let f:=meterForest s (some p);let u:=unchangedForestMeter ss
      (⟨f.value++u.value,f.work+u.work+2*f.value.length+8⟩:Charged Forest))
    (meterEdges s).value (128*(N+1)^3+unchangedForestPolynomial N+12) (by
     intro p hp
     have ep:p∈DepthOne.edges s:=by simpa only [meterEdges_value] using hp
     have f:=meterForest_bound s (some p) N nodes (by
      intro v hv;cases hv
      exact Nat.le_trans (vertices_address s p (edges_mem_vertices s p ep)) nodes)
     have fl:=(forest_cells s (some p)).1
     simp only [meterForest_value];omega)
   have headmul:=Nat.mul_le_mul_left (128*(N+1)^3+unchangedForestPolynomial N+16) (Nat.add_le_add_right elen 1)
   have tlen:(oneCutsForestMeter ss).value.length≤N:=by
    rw [oneCutsForestMeter_value];exact Nat.le_trans (oneCutsForest_count ss) tails
   have leaf:=meterLeaves_cap s N nodes
   have lift:=meterMap_bound (fun F:Forest=>let l:=meterLeaves s
       (⟨l.value::F,l.work+8⟩:Charged Forest)) (oneCutsForestMeter ss).value (8*(N+1)^2+8)
     (by intro _ _;simp only [];omega)
   have liftmul:=Nat.mul_le_mul_left (8*(N+1)^2+12) (Nat.add_le_add_right tlen 1)
   have headlen:(meterMap (fun p=>let f:=meterForest s (some p);let u:=unchangedForestMeter ss
      (⟨f.value++u.value,f.work+u.work+2*f.value.length+8⟩:Charged Forest)) (meterEdges s).value).value.length≤N:=by
    simp only [meterMap_value,List.length_map];exact elen
   dsimp only at head lift headlen
   have headcap:=Nat.le_trans head headmul
   have liftcap:=Nat.le_trans lift liftmul
   have step:
    (meterEdges s).work+
     (meterMap (fun p=>let f:=meterForest s (some p);let u:=unchangedForestMeter ss
      (⟨f.value++u.value,f.work+u.work+2*f.value.length+8⟩:Charged Forest)) (meterEdges s).value).work+
     (meterMap (fun F:Forest=>let l:=meterLeaves s
       (⟨l.value::F,l.work+8⟩:Charged Forest)) (oneCutsForestMeter ss).value).work+
     2*(meterMap (fun p=>let f:=meterForest s (some p);let u:=unchangedForestMeter ss
      (⟨f.value++u.value,f.work+u.work+2*f.value.length+8⟩:Charged Forest)) (meterEdges s).value).value.length+12≤oneCutStepPolynomial N:=by
    unfold oneCutStepPolynomial
    dsimp only at *
    omega
   have total:=Nat.add_le_add step tail
   simpa only [oneCutsForestMeter,List.length_cons,Nat.mul_add,Nat.mul_one,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using total

def pretestConstructionPolynomial (N : Nat):=
 unchangedForestPolynomial N+oneCutStepPolynomial N*N+6

theorem pretestCandidatesMeter_bound (ss : List Tree) (N : Nat)
 (sn:sourceNodes ss≤N) (sl:ss.length≤N) :
 (pretestCandidatesMeter ss).work≤pretestConstructionPolynomial N:=by
 have u:=unchangedForestMeter_bound ss N sn sl
 have c:=oneCutsForestMeter_bound ss N sn sl
 have mul:=Nat.mul_le_mul_left (oneCutStepPolynomial N) sl
 simp only [pretestCandidatesMeter,pretestConstructionPolynomial];omega
end OrdinaryDispatch.Hard2SourceWork
