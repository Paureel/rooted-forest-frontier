import ELPretestBounds
namespace OrdinaryDispatch.EarlyLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence CherryBranching

def meterCherries : Tree→Charged (List (RMAF.Vertex×Nat×Nat))
 | .leaf _=>⟨[],2⟩
 | .node l r=>let a:=meterCherries l;let b:=meterCherries r
  ⟨match l,r with
   | .leaf x,.leaf y=>[([],x,y)]
   | _,_=>a.value.map (fun (p,x,y)=>(false::p,x,y))++b.value.map (fun (p,x,y)=>(true::p,x,y)),
   a.work+b.work+8*(a.value.length+b.value.length+1)+4⟩
@[simp] theorem meterCherries_value (T : Tree) : (meterCherries T).value=cherries T := by
 induction T with
 | leaf x=>rfl
 | node l r il ir=>cases l <;> cases r <;> simp_all [meterCherries,cherries]
theorem cherries_length (T : Tree) : (cherries T).length≤treeNodes T := by
 induction T with
 | leaf x=>simp [cherries,treeNodes]
 | node l r il ir=>cases l <;> cases r <;> simp_all [cherries,treeNodes] <;> omega

theorem meterCherries_bound (T : Tree) (N : Nat) (tn : treeNodes T≤N) :
 (meterCherries T).work≤16*(N+1)*treeNodes T := by
 induction T with
 | leaf x=>simp only [meterCherries,treeNodes,Nat.mul_one];omega
 | node l r il ir=>
  have ln : treeNodes l≤N:=by simp only [treeNodes] at tn;omega
  have rn : treeNodes r≤N:=by simp only [treeNodes] at tn;omega
  have a:=il ln;have b:=ir rn;have al:=cherries_length l;have bl:=cherries_length r
  simp only [meterCherries,meterCherries_value,treeNodes,Nat.mul_add,Nat.mul_one] at a b tn ⊢;omega

def meterCherryCandidates (T S : Tree) : Charged (List Candidate) :=
 let c:=meterCherries T
 let m:=meterMap (fun (p,a,b)=>let cuts:=meterPendant S a b;⟨(⟨p,a,b,cuts.value⟩:Candidate),cuts.work+4⟩) c.value
 ⟨m.value,c.work+m.work+2⟩
@[simp] theorem meterCherryCandidates_value (T S) : (meterCherryCandidates T S).value=candidates T S := by
 simp [meterCherryCandidates,candidates,CherryBranching.cuts]

theorem pendant_length (S : Tree) (a b : Nat) : (HardParent.pendantOriginal S a b).length≤treeNodes S := by
 exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (vertices_length S))

theorem cherry_candidate_cuts (T S : Tree) (c : Candidate) (hc : c∈candidates T S) :
 c.originalCuts.length≤treeNodes S := by
 have h:=(candidate_sound hc).2
 rw [h]
 exact pendant_length S c.a c.b

theorem meterCherryCandidates_bound (T S : Tree) (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterCherryCandidates T S).work≤1024*(N+1)^5 := by
 have c:=meterCherries_bound T N tn
 have cl:=Nat.le_trans (cherries_length T) tn
 have cc:=Nat.mul_le_mul_left (16*(N+1)) (Nat.le_trans tn (Nat.le_succ N))
 let f : RMAF.Vertex×Nat×Nat→Charged Candidate:=fun (p,a,b)=>let cuts:=meterPendant S a b;⟨⟨p,a,b,cuts.value⟩,cuts.work+4⟩
 have point (x : RMAF.Vertex×Nat×Nat) : (f x).work≤512*(N+1)^4+4:=by
  obtain ⟨p,a,b⟩:=x;exact Nat.add_le_add_right (meterPendant_bound S a b N sn) 4
 have map:=meterMap_bound f (cherries T) (512*(N+1)^4+4) (fun x _=>point x)
 have pos : 1≤(N+1)^4:=Nat.one_le_pow _ _ (by omega)
 have coeff : 512*(N+1)^4+4+4≤520*(N+1)^4:=by omega
 have scaled:=Nat.mul_le_mul coeff (Nat.add_le_add_right cl 1)
 have mm : (meterMap f (cherries T)).work≤520*(N+1)^5:=Nat.le_trans map
  (by simpa only [show 5=4+1 from rfl,Nat.pow_succ,Nat.mul_assoc] using scaled)
 have l:=pow_mono N 2 5 (by decide)
 have cc' : (meterCherries T).work≤16*(N+1)^5:=Nat.le_trans c
  (Nat.le_trans cc (by simpa only [Nat.pow_two,Nat.mul_assoc] using Nat.mul_le_mul_left 16 l))
 have pp : 1≤(N+1)^5:=Nat.one_le_pow _ _ (by omega)
 simp only [meterCherryCandidates,meterCherries_value];change (meterCherries T).work+(meterMap f (cherries T)).work+2≤_;omega

/-- Later priority scans may be overcharged after an earlier successful scan.
Every actually visited candidate is included, and cut-list lengths are scanned. -/
def meterSelect (T S : Tree) : Charged (Option (Priority×Candidate)) :=
 let c:=meterCherryCandidates T S
 let common:=meterFind (fun x:Candidate=>⟨x.originalCuts.isEmpty,1⟩) c.value
 let one:=meterFind (fun x:Candidate=>⟨x.originalCuts.length==1,4*(x.originalCuts.length+1)⟩) c.value
 let high:=meterFind (fun x:Candidate=>⟨decide (3≤x.originalCuts.length),4*(x.originalCuts.length+1)⟩) c.value
 ⟨match common.value with
  | some x=>some (.common,x)
  | none=>match one.value with
    | some x=>some (.one,x)
    | none=>match high.value with
      | some x=>some (.high,x)
      | none=>c.value.head?.map (fun x=>(.hard2,x)),
  c.work+common.work+one.work+high.work+8⟩
@[simp] theorem meterSelect_value (T S) : (meterSelect T S).value=select T S := by
 simp only [meterSelect,meterCherryCandidates_value,meterFind_value,select]
 repeat first | rfl | split

theorem meterSelect_bound (T S : Tree) (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterSelect T S).work≤2048*(N+1)^5 := by
 have c:=meterCherryCandidates_bound T S N tn sn
 have cl : (candidates T S).length≤N:=by simpa [candidates] using Nat.le_trans (cherries_length T) tn
 have point (x : Candidate) (hx : x∈candidates T S) : 4*(x.originalCuts.length+1)≤4*(N+1):=by have h:=cherry_candidate_cuts T S x hx;omega
 have common:=meterFind_bound (fun x:Candidate=>⟨x.originalCuts.isEmpty,1⟩) (candidates T S) (4*(N+1)) (by intro x hx;dsimp;omega)
 have one:=meterFind_bound (fun x:Candidate=>⟨x.originalCuts.length==1,4*(x.originalCuts.length+1)⟩) (candidates T S) (4*(N+1)) point
 have high:=meterFind_bound (fun x:Candidate=>⟨decide (3≤x.originalCuts.length),4*(x.originalCuts.length+1)⟩) (candidates T S) (4*(N+1)) point
 have scale:=Nat.mul_le_mul (show 4*(N+1)+4≤8*(N+1) by omega) (Nat.add_le_add_right cl 1)
 have co:=cap_lift N 8 2 5 _ (Nat.le_trans common (by simpa only [Nat.pow_two,Nat.mul_assoc] using scale)) (by decide)
 have on:=cap_lift N 8 2 5 _ (Nat.le_trans one (by simpa only [Nat.pow_two,Nat.mul_assoc] using scale)) (by decide)
 have hi:=cap_lift N 8 2 5 _ (Nat.le_trans high (by simpa only [Nat.pow_two,Nat.mul_assoc] using scale)) (by decide)
 have pos : 1≤(N+1)^5:=Nat.one_le_pow _ _ (by omega)
 simp only [meterSelect,meterCherryCandidates_value];omega

end OrdinaryDispatch.EarlyLocalWork
