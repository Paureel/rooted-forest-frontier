import ELPretest
namespace OrdinaryDispatch.EarlyLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence

theorem edges_mem_vertices (S : Tree) (v : RMAF.Vertex) (hv : v∈DepthOne.edges S) : v∈HardParent.vertices S := by
 rw [vertices_depthone]
 cases S with
 | leaf x=>simp [DepthOne.edges] at hv
 | node l r=>exact List.mem_cons_of_mem [] hv

theorem candidate_address (S : Tree) (c : Option RMAF.Vertex) (hc : c∈DepthOne.candidates S)
 (v : RMAF.Vertex) (eq : c=some v) : v.length≤treeNodes S := by
 subst c
 have hm : v∈DepthOne.edges S:=by simpa [DepthOne.candidates] using hc
 exact vertices_address S v (edges_mem_vertices S v hm)

theorem meterCandidates_bound (S : Tree) (N : Nat) (sn : treeNodes S≤N) :
 (meterCandidates S).work≤32*(N+1)^2 := by
 have v:=meterVertices_bound S N sn
 have vv:=Nat.mul_le_mul_left (8*(N+1)) (Nat.le_trans sn (Nat.le_succ N))
 have p : N+1≤(N+1)^2:=by simpa using pow_mono N 1 2 (by decide)
 have pos : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
 simp only [meterCandidates,meterEdges,meterVertices_value,vertices_length,List.length_tail]
 simp only [Nat.pow_two,Nat.mul_assoc] at v vv p pos ⊢;omega

theorem meterCandidate_bound (T S : Tree) (c : Option RMAF.Vertex) (hc : c∈DepthOne.candidates S)
 (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterCandidate T S c).work≤300000*(N+1)^5 := by
 have af:=forest_cells S c
 have m : 2*(N+1)+1≤3*(N+1):=by omega
 have f:=cap_lift N 128 3 5 _ (meterForest_bound S c N sn (fun v hv=>Nat.le_trans (candidate_address S c hc v hv) sn)) (by decide)
 have a:=meterAgreement_bound T S (DepthOne.forest S c) (2*(N+1)) (by omega) (by omega) (by omega) (by omega)
 have lifted:=Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left m 5)
 have big : 1024*(3*(N+1))^5=248832*(N+1)^5 := by simp only [Nat.mul_pow];simp_arith [Nat.mul_assoc]
 have aa : (meterAgreement T S (DepthOne.forest S c)).work≤248832*(N+1)^5:=Nat.le_trans a (big ▸ lifted)
 have pos : 1≤(N+1)^5:=Nat.one_le_pow _ _ (by omega)
 simp only [meterCandidate,meterForest_value];omega

/-- All no-cut and one-cut checks, valid and invalid, and all best-tail
comparisons are included. No agreement or successful-check premise is needed. -/
theorem meterPretest_bound (T S : Tree) (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterPretest T S).work≤400000*(N+1)^6 := by
 have p:=cap_lift N 128 2 6 _ (meterOrdinaryProper_bound T S N tn sn) (by decide)
 have c:=cap_lift N 32 2 6 _ (meterCandidates_bound S N sn) (by decide)
 have b:=meterBest_bound DepthOne.cutCost (meterCandidate T S) (DepthOne.candidates S) (300000*(N+1)^5)
  (fun x hx=>meterCandidate_bound T S x hx N tn sn)
 have coeff : 300000*(N+1)^5+10≤300010*(N+1)^5:=by have pos:=Nat.one_le_pow 5 (N+1) (by omega);omega
 have scale:=Nat.mul_le_mul coeff (Nat.add_le_add_right sn 1)
 rw [candidates_length] at b
 have bb : (meterBest DepthOne.cutCost (meterCandidate T S) (DepthOne.candidates S)).work≤300010*(N+1)^6:=
  Nat.le_trans b (by simpa only [show 6=5+1 from rfl,Nat.pow_succ,Nat.mul_assoc] using scale)
 have pos : 1≤(N+1)^6:=Nat.one_le_pow _ _ (by omega)
 simp only [meterPretest,meterCandidates_value]
 split <;> simp only [Charged.work] <;> omega

end OrdinaryDispatch.EarlyLocalWork
