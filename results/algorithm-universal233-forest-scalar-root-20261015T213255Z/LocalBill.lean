import MaterialBounds
namespace GenericForest.LocalPolynomial
open RMAF ForestState Universal233 Universal233.PaidQueries Universal233.CoreWork Universal233.CoreProgram Universal233.WholeSourceWork

theorem overlap_body_bound (t : Tree) (ss : List Tree) (q M : Nat) (h : Overlap)
 (hp : proper (some t) ss=true) (size : (leaves t).length≤M) (budget : q≤M) (selected : overlap t ss=some h) :
 overlapBill t ss+generationBill t ss h.left h.vertex q+generationBill t ss h.right h.vertex q+
 ((branches t ss h q).map fun io=>materializationBill t ss q io.1 io.2).sum+
 inspectionBill (some t) ss q*((branches t ss h q).length+1)≤
 (overlapCap M+2*generationCap M+12*materialCap M+13*inspectCap M)*2^q := by
 obtain ⟨s,r,hi,hj,_,hv,_⟩:=selected_parents_distinct t ss hp h selected
 have address : h.vertex.length≤M:=by have v:=minimal_address (leaves s) t h.vertex hv;omega
 have a:=generation_bill_bound t ss q M h.left s h.vertex hp size budget hi address
 have b:=generation_bill_bound t ss q M h.right r h.vertex hp size budget hj address
 have materials:=materializations_bound t ss q M h hp size budget selected
 have search:=overlap_bill_bound t ss M hp size
 have inspection:=inspection_bound (some t) ss q M hp size budget
 have pow : 1≤2^q:=Nat.pow_pos (by decide)
 have searchScaled:=Nat.mul_le_mul_left (overlapCap M) pow
 simp only [Nat.mul_one] at searchScaled
 have count:=(branches_output_count t ss h q)
 have countPlus : (branches t ss h q).length+1≤13*2^q:=by omega
 have repeated:=Nat.mul_le_mul inspection countPlus
 have algebra : inspectCap M*(13*2^q)=(13*inspectCap M)*2^q:=by ac_rfl
 rw [algebra] at repeated
 simp only [Nat.add_mul,Nat.mul_assoc] at materials repeated ⊢
 omega

theorem zero_schedule_recursive {P A : Type} (rec : P → Nat → Option (Nat × A)) (q : Nat) (js : List (Job P A)) :
 (meterSchedule rec (fun _ _=>0) q js).recursiveWork=0 := by
 rw [(meterSchedule_trace rec (fun _ _=>0) q js).2]
 have zero (xs : List (P × Nat)) : (xs.map (fun _=>(0:Nat))).sum=0 := by induction xs <;> simp_all
 exact zero _

/-- Every literal local source charge, including failed prefixes and copies, is retained. -/
theorem nonrecursive_bill_polynomial (ordinary : FrontierWork.Ordinary) (T : Option Tree) (ss : List Tree) (q M : Nat)
 (hp : proper T ss=true) (size : (labels T).length≤M) (budget : q≤M) :
 nonrecursiveBill ordinary (fun _ _ _=>0) T ss q≤overheadPolynomial M*2^q := by
 have inspection:=inspection_bound T ss q M hp size budget
 have pow : 1≤2^q:=Nat.pow_pos (by decide)
 have paidInspection:=Nat.mul_le_mul_left (inspectCap M) pow
 simp only [Nat.mul_one] at paidInspection
 have base : inspectionBill T ss q≤overheadPolynomial M*2^q := by
  have coeff : inspectCap M≤overheadPolynomial M:=by unfold overheadPolynomial;omega
  exact Nat.le_trans (Nat.le_trans inspection paidInspection) (Nat.mul_le_mul_right (2^q) coeff)
 unfold nonrecursiveBill
 split
 · rename_i active
   split
   · simpa only [Nat.add_zero] using base
   · simpa only [Nat.add_zero] using base
   · rename_i _ _ t notsingle
     split
     · split
       · simpa only [Nat.add_zero] using base
       · rename_i js hj
         change inspectionBill (some t) ss q+
          ((meterSchedule (FrontierWork.pairCallback ordinary) (fun _ _=>0) q js).callerWork+
           (meterSchedule (FrontierWork.pairCallback ordinary) (fun _ _=>0) q js).recursiveWork)≤_
         rw [zero_schedule_recursive,Nat.add_zero]
         have caller:=meterSchedule_caller (FrontierWork.pairCallback ordinary) (fun _ _=>0) q js
         rw [jobs_length t ss js hj] at caller
         have slots:=(state_size_bounds (some t) ss hp M size).2.2
         have callerCap:=Nat.mul_le_mul_left 32 (Nat.add_le_add_right slots 1)
         have callerScaled:=Nat.mul_le_mul_left (32*(2*M+1)) pow
         simp only [Nat.mul_one] at callerScaled
         unfold overheadPolynomial
         simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc] at callerScaled callerCap ⊢
         omega
     · rename_i h hh
       have bodies:=overlap_body_bound t ss q M h hp size budget hh
       unfold overheadPolynomial
       simp only [Nat.add_mul,Nat.mul_assoc] at bodies ⊢
       omega
 · simpa only [Nat.add_zero] using base

theorem two_power_le (c : Rat) (hc : 2≤c) (q : Nat) : (2:Rat)^q≤c^q := by
 induction q with
 | zero => simpa only [Rat.pow_zero] using (Rat.le_refl (a:=(1:Rat)))
 | succ q ih =>
  have cp : 0<c:=by grind
  have a:=Rat.mul_le_mul_of_nonneg_right ih (by decide : 0≤(2:Rat))
  have b:=Rat.mul_le_mul_of_nonneg_left hc (show 0≤c^q from Rat.le_of_lt (Rat.pow_pos cp))
  simpa only [Rat.pow_succ] using Rat.le_trans a b

/-- Concrete polynomial zero-ordinary-work local premise, independent of callback bills. -/
theorem polynomial_local_overhead (ordinary : FrontierWork.Ordinary) (T : Option Tree) (N Q : Nat)
 (c : Rat) (hc : 2≤c) (size : (labels T).length≤N) :
 FrontierWork.LocalOverheadBound ordinary T Q c (overheadPolynomial (N+Q+2):Rat) := by
 intro ss q hq hp
 have natBound:=nonrecursive_bill_polynomial ordinary T ss q (N+Q+2) hp (by omega) (by omega)
 have cast:=Rat.natCast_le_natCast.2 natBound
 rw [Rat.natCast_mul,Rat.natCast_pow] at cast
 exact Rat.le_trans cast (Rat.mul_le_mul_of_nonneg_left (two_power_le c hc q) Rat.natCast_nonneg)

theorem source_work_polynomial_size_capped (ordinary : FrontierWork.Ordinary) (W : FrontierWork.OrdinaryWork)
 (T : Option Tree) (N Q : Nat) (c D : Rat) (hc : 2<c) (hD : 0≤D) (size : (labels T).length≤N)
 (bill : FrontierSize.SizeCappedOrdinaryBillBound W N Q c D) (ss : List Tree) (q : Nat) (hq : q≤Q) (hp : proper T ss=true) :
 sourceWork ordinary W T ss q≤(D+FrontierWork.geometric c*(overheadPolynomial (N+Q+2):Rat))*c^q :=
 FrontierSize.source_work_bound_size_capped ordinary W T N Q c _ D hc Rat.natCast_nonneg hD
  (polynomial_local_overhead ordinary T N Q c (Rat.le_of_lt hc) size) bill ss q hq hp size
end GenericForest.LocalPolynomial
