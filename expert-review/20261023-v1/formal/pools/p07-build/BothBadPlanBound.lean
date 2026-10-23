import BothBadPlannerBounds
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.BothBad Universal233.PaidQueries

def cheapOutputCoefficient (N Q : Nat):=generationPolynomial N*(Q+1)+N*(12*(N+1)+8)

theorem cheapOutputs_uniform (S : Tree) (A B D : List Nat) (r q N Q : Nat)
 (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (dl:D.length≤N)
 (rq:r≤q) (budget:q≤Q) :
 (generatedOutputsMeter S (cheapColorMeter A B D) r).work≤cheapOutputCoefficient N Q*2^(q+1) ∧
 (generatedOutputsMeter S (cheapColorMeter A B D) r).value.length≤3*2^(q+1) ∧
 (∀o,o∈(generatedOutputsMeter S (cheapColorMeter A B D) r).value→o.sourceCuts.length≤Q):=by
 have gen:=generatedOutputsMeter_bound S (cheapColorMeter A B D) r
 have env:=generationEnvelope_uniform S N r sn
 have pow:=Nat.pow_le_pow_right (show 1≤2 by decide) (show r+1≤q+1 by omega)
 have env':generationEnvelope S r≤generationPolynomial N*(Q+1)*2^(q+1):=
  Nat.le_trans env (Nat.mul_le_mul (Nat.mul_le_mul_left _ (show r+1≤Q+1 by omega)) pow)
 have color:=charged_color_sum (leaves S) (cheapColorMeter A B D) (12*(N+1)+8)
  (by intro x _;exact sideTaggedMeter_bound B A D x N bl al dl)
 have lc:=Nat.mul_le_mul_right (12*(N+1)+8) (Nat.le_trans (leaves_nodes S) sn)
 have lift:=Nat.mul_le_mul_left (N*(12*(N+1)+8)) (show 1≤2^(q+1) from Nat.two_pow_pos _)
 have count:=generate_output_count S (fun x=>(cheapColorMeter A B D x).value) r
 have cp:=Nat.pow_le_pow_right (show 1≤2 by decide) (show min r ((leaves S).length-1)+1≤q+1 by omega)
 constructor
 · simp only [cheapOutputCoefficient,Nat.add_mul];omega
 · constructor
   · simp only [generatedOutputsMeter_value];omega
   · intro o mem
     rw [generatedOutputsMeter_value] at mem
     exact Nat.le_trans (SourceCoverage.generate_output_budget S _ r o mem) (by omega)

theorem reuseOutputs_uniform (S : Tree) (A B D : List Nat) (probe : List CoreProgram.Output)
 (q N Q : Nat) (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (dl:D.length≤N)
 (budget:q≤Q) (len:probe.length≤3*2^(q+1)) (cuts:∀o,o∈probe→o.sourceCuts.length≤Q) :
 (reuseOutputsMeter S (cheapColorMeter A B D) probe q).work≤cheapOutputCoefficient N Q*2^(q+1)+4 ∧
 (reuseOutputsMeter S (cheapColorMeter A B D) probe q).value.length≤3*2^(q+1) ∧
 (∀o,o∈(reuseOutputsMeter S (cheapColorMeter A B D) probe q).value→o.sourceCuts.length≤Q):=by
 have gen:=cheapOutputs_uniform S A B D q q N Q sn al bl dl (Nat.le_refl _) budget
 simp only [reuseOutputsMeter]
 split
 · simp only [Charged.work,Charged.value];exact ⟨by omega,gen.2⟩
 · simp only [Charged.work,Charged.value];exact ⟨by omega,len,cuts⟩

def bothBadPlanCoefficient (N Q : Nat):=
 4*cheapOutputCoefficient N Q+(2*Q+24)*6+cheapPlanFixedPolynomial N+128

/-- Full literal planner work: both q3 probes, every branch generator,
reuse, guard, entry filter and append. The original q is retained. -/
theorem bothBadPlanMeter_bound (S T : Tree) (A B C D : List Nat) (q N Q : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (dl:D.length≤N)
 (budget:q≤Q) :
 (bothBadPlanMeter S T A B C D q).work≤bothBadPlanCoefficient N Q*2^(q+1):=by
 have pos:1≤2^(q+1):=Nat.two_pow_pos _
 have fixed:=Nat.mul_le_mul_left (cheapPlanFixedPolynomial N+128) pos
 by_cases low:q<3
 · simp only [bothBadPlanMeter,low,ite_true,Charged.work]
   have minimum:128*2^(q+1)≤bothBadPlanCoefficient N Q*2^(q+1):=Nat.mul_le_mul_right _ (by unfold bothBadPlanCoefficient;omega)
   omega
 · have three:3≤q:=by omega
   have a:=cheapOutputs_uniform S A B D 3 q N Q sn al bl dl three budget
   have b:=cheapOutputs_uniform S B A D 3 q N Q sn bl al dl three budget
   have x:=cheapOutputs_uniform S A B D q q N Q sn al bl dl (Nat.le_refl _) budget
   have y:=cheapOutputs_uniform S B A D q q N Q sn bl al dl (Nat.le_refl _) budget
   have ra:=reuseOutputs_uniform S A B D _ q N Q sn al bl dl budget a.2.1 a.2.2
   have rb:=reuseOutputs_uniform S B A D _ q N Q sn bl al dl budget b.2.1 b.2.2
   have cpA:=cheapPlanMeter_bound S T A B C D q N Q tn sn al dl _ _ a.2.2 rb.2.2
   have cpB:=cheapPlanMeter_bound S T B A C D q N Q tn sn bl dl _ _ b.2.2 ra.2.2
   have cc:∀o,o∈(appendOutputsMeter
      (generatedOutputsMeter S (cheapColorMeter A B D) q)
      (generatedOutputsMeter S (cheapColorMeter B A D) q)).value→o.sourceCuts.length≤Q:=by
    intro o hm
    simp only [appendOutputsMeter_value,List.mem_append] at hm
    exact hm.elim (x.2.2 o) (y.2.2 o)
   have ent:=entriesMeter_bound q Q .full _ cc
   have sumAB:(generatedOutputsMeter S (cheapColorMeter A B D) 3).value.length+
     (reuseOutputsMeter S (cheapColorMeter B A D) (generatedOutputsMeter S (cheapColorMeter B A D) 3).value q).value.length≤6*2^(q+1):=by omega
   have sumBA:(generatedOutputsMeter S (cheapColorMeter B A D) 3).value.length+
     (reuseOutputsMeter S (cheapColorMeter A B D) (generatedOutputsMeter S (cheapColorMeter A B D) 3).value q).value.length≤6*2^(q+1):=by omega
   have mAB:=Nat.mul_le_mul_left (2*Q+24) sumAB
   have mBA:=Nat.mul_le_mul_left (2*Q+24) sumBA
   rw [←Nat.mul_assoc] at mAB mBA
   have cpA':(cheapPlanMeter S T A B C D q
      (generatedOutputsMeter S (cheapColorMeter A B D) 3).value
      (reuseOutputsMeter S (cheapColorMeter B A D) (generatedOutputsMeter S (cheapColorMeter B A D) 3).value q).value).work≤
      cheapPlanFixedPolynomial N+((2*Q+24)*6)*2^(q+1)+64:=by omega
   have cpB':(cheapPlanMeter S T B A C D q
      (generatedOutputsMeter S (cheapColorMeter B A D) 3).value
      (reuseOutputsMeter S (cheapColorMeter A B D) (generatedOutputsMeter S (cheapColorMeter A B D) 3).value q).value).work≤
      cheapPlanFixedPolynomial N+((2*Q+24)*6)*2^(q+1)+64:=by omega
   have outlen:(appendOutputsMeter
      (generatedOutputsMeter S (cheapColorMeter A B D) q)
      (generatedOutputsMeter S (cheapColorMeter B A D) q)).value.length≤6*2^(q+1):=by
    simp only [appendOutputsMeter_value,List.length_append];omega
   have entmul:=Nat.mul_le_mul (show 2*Q+20≤2*Q+24 by omega) outlen
   rw [←Nat.mul_assoc] at entmul
   have ent':(entriesMeter q .full (appendOutputsMeter
      (generatedOutputsMeter S (cheapColorMeter A B D) q)
      (generatedOutputsMeter S (cheapColorMeter B A D) q)).value).work≤((2*Q+24)*6)*2^(q+1)+2:=by omega
   have fixed':cheapPlanFixedPolynomial N≤cheapPlanFixedPolynomial N*2^(q+1):=by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (cheapPlanFixedPolynomial N) pos
   simp only [bothBadPlanMeter,low,ite_false]
   split
   · split
     · simp only [appendOutputsMeter,Charged.work]
       change _≤(4*cheapOutputCoefficient N Q+((2*Q+24)*6)+cheapPlanFixedPolynomial N+128)*2^(q+1)
       rw [Nat.add_mul,Nat.add_mul,Nat.add_mul]
       have four:4*cheapOutputCoefficient N Q*2^(q+1)=4*(cheapOutputCoefficient N Q*2^(q+1)):=Nat.mul_assoc _ _ _
       rw [four]
       simp only [appendOutputsMeter,Charged.value] at ent'
       omega
     · simp only [Charged.work]
       change _≤(4*cheapOutputCoefficient N Q+((2*Q+24)*6)+cheapPlanFixedPolynomial N+128)*2^(q+1)
       rw [Nat.add_mul,Nat.add_mul,Nat.add_mul]
       rw [Nat.mul_assoc 4]
       omega
   · simp only [Charged.work]
     change _≤(4*cheapOutputCoefficient N Q+((2*Q+24)*6)+cheapPlanFixedPolynomial N+128)*2^(q+1)
     rw [Nat.add_mul,Nat.add_mul,Nat.add_mul]
     rw [Nat.mul_assoc 4]
     omega
end OrdinaryDispatch.Hard2SourceWork
