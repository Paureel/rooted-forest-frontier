import WholeFunctional
import CompletePolynomialExplicit
namespace RebasedSourceCounter20261022
open RMAF Universal233 OrdinaryDispatch
set_option autoImplicit false
/- Only affected support theorem proofs are reconstructed here. Every data and
   meter definition remains the literal canonical fca object. See REBASE-ORIGINS. -/

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/ClosedPayload.lean:26
section
open Universal233.Rule5LocalWork
open OrdinaryDispatch
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller
theorem closed_payload (T S : Tree) (q : Nat) {F : List (List Nat)}
 (hp : DepthOne.proper T S=true) (answer : actual T S q=some F) :
 F.flatten.length=(leaves T).length ∧ F.length≤(leaves T).length ∧
 (∀x,x∈F.flatten →x∈leaves T) ∧ cells F≤2*(leaves T).length := by
 have sound := OrdinaryDispatch.FastOrdinary.query_sound
   (CompletedFunctional233.query_correct q T S hp) answer
 have nd : (leaves T).Nodup := by
   simp only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at hp
   exact hp.1.1
 exact agreement_payload T S F nd sound.1
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/CommonCutoffPayload.lean:19
section
open Universal233.Rule5ClosedSource
open OrdinaryDispatch
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.FastOrdinary
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence
theorem cutoff_sound (q : Nat) : CallbackSound (cutoff OrdinaryDispatch.FastOrdinary.solve q) := by
 intro T S r F hp hf
 by_cases below:r<q
 · have returned:OrdinaryDispatch.FastOrdinary.solve r T S=some F:=by simpa only [cutoff,below,ite_true] using hf
   exact (query_sound (CompletedFunctional233.query_correct r T S hp) returned).1
 · simp [cutoff,below] at hf
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/ActualCaller.lean:40
section
open Universal233.Rule5ClosedSource
open OrdinaryDispatch
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryCommonSplit.Source
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion OrdinaryDispatch.FastOrdinary
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5SelectedLocalWork
open ClassifierCheckFee PaidLiteralDecisionWork
theorem actual_rule5_bound {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch:CherryAt T i a b) (ad:admitted T S a b=true) (q N Q L : Nat) (domain:InputDomain T S q N Q L) :
 ((actualRule5Source (fun _ _ _=>0) T S a b q).work:Rat)≤(C5 N Q L:Rat)*Rule5ActualTrace.base^q := by
 have hp:=admitted_proper ad
 have eq:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
 have targetCap:=domain.size
 have sourceCap:(leaves S).length≤N:=by omega

 have pow:=call_base_pow_ge_one q
 have positive:0≤Rule5ActualTrace.base^q:=Rat.le_trans (by decide +kernel) pow
 -- The two wrapper inspections use the explicit spare constant in C5.
 -- First obtain the tighter source bound before the coefficient's spare 4.
 obtain ⟨z,sel0,_⟩:=final_classification_complete ch ad
 have sel:(finalMeter checkFee T S a b).value=some z:=by rw [final_value];exact sel0
 have local0:=dispatch_concrete_local (actualCallback q) (cutoff_sound q) ch ad hp q L sel domain.targetLabels domain.sourceLabels
 have cap:=selected_prefix_cap T S domain.size sourceCap z
 have localNat:(source (actualCallback q) (fun _ _ _=>0) T S a b q).work+2≤prefixCap N+selectedForestDebit (actualCallback q) checkFee (literalFee T S a b) T S a b q z+2:=by omega
 have lr:=Rat.natCast_le_natCast.2 localNat
 simp only [Rat.natCast_add,Rat.natCast_ofNat] at lr
 have forests:=selected_forest_debit_bound (actualCallback q) ch ad q N Q sel domain.size sourceCap domain.budget
 have debit:=Rat.le_trans forests (forest_envelope_coefficient N Q L q)
 have prefScaled:=Rat.mul_le_mul_of_nonneg_left pow (Rat.natCast_nonneg (a:=prefixCap N+2))
 rw [Rat.mul_one,Rat.natCast_add,Rat.natCast_ofNat] at prefScaled
 have total:=Rat.le_trans (Rat.add_le_add_right.mpr prefScaled) (Rat.add_le_add_left.mpr debit)
 have c0:(prefixCap N:Rat)+2+(80*(2^50*(N+Q+L+2)^8):Nat)≤(C5 N Q L:Rat):=by
  unfold C5;simp only [Rat.natCast_add,Rat.natCast_ofNat]
  have h:(0:Rat)≤2:=by decide +kernel
  have step:((prefixCap N:Rat)+(80*(2^50*(N+Q+L+2)^8):Nat))+2≤((prefixCap N:Rat)+(80*(2^50*(N+Q+L+2)^8):Nat))+4:=
   Rat.add_le_add_left.mpr (by decide +kernel : (2:Rat)≤4)
  simpa only [Rat.add_assoc,Rat.add_comm,Rat.add_left_comm] using step
 have scaled:=Rat.mul_le_mul_of_nonneg_right c0 positive
 change (((source (actualCallback q) (fun _ _ _=>0) T S a b q).work+2:Nat):Rat)≤_
 rw [Rat.natCast_add,Rat.natCast_ofNat]
 apply Rat.le_trans lr
 apply Rat.le_trans (b:=((prefixCap N:Rat)+2+(80*(2^50*(N+Q+L+2)^8):Nat))*Rule5ActualTrace.base^q) ?_ scaled
 have total':(prefixCap N:Rat)+2+selectedForestDebit (actualCallback q) checkFee (literalFee T S a b) T S a b q z≤
  ((prefixCap N:Rat)+2+(80*(2^50*(N+Q+L+2)^8):Nat))*Rule5ActualTrace.base^q:=by
  apply Rat.le_trans (Rat.add_le_add_left.mpr debit)
  simpa only [Rat.add_mul] using Rat.add_le_add_right.mpr prefScaled
 simpa only [actualRule5Source,rule5AnswerSource,Rat.add_assoc,Rat.add_comm,Rat.add_left_comm] using total'
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/AdmittedRouteBinding.lean:48
section
open Universal233.Rule5ClosedSource
open OrdinaryDispatch
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion OrdinaryDispatch.FastOrdinary OrdinaryDispatch.Hard2SourceWork
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5SelectedLocalWork
open ClassifierCheckFee PaidLiteralDecisionWork CherryBranching Hard2Overlap
theorem admitted_route_bound {T S : Tree} {c d : Candidate} (q N Q L : Nat)
 (hp:DepthOne.proper T S=true)
 (forward:CherryBranching.select T S=some (.hard2,c))
 (reverse:CherryBranching.select S T=some (.hard2,d))
 (noT:Rule4.select T S=none) (noS:Rule4.select S T=none)
 (route:(hard2FrontMeter T S c q).value=.admittedRule5) (domain:InputDomain T S q N Q L) :
 ((admittedRouteSource (fun _ _ _=>0) T S c q).work:Rat)≤(C5 N Q L:Rat)*(233/100:Rat)^q := by
 have ad:=actual_admitted_route q hp forward reverse noT noS route
 have ch:CherryAt T c.parent c.a c.b:=(selected_actual forward).1
 simpa only [admittedRouteSource,Rule5ActualTrace.base] using actual_rule5_bound ch ad q N Q L domain
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/ClosedRule5Join.lean:23
section
open OrdinaryDispatch.GoodPairGlobalAssembly
open OrdinaryDispatch
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open OrdinaryDispatch.WorkRecursion OrdinaryDispatch.WorkIntegration OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.ExtendedSourceAssembly OrdinaryDispatch.FastOrdinary
open Universal233.Rule5ClosedSource OrdinaryDispatch.GlobalNumeric
theorem closedRule5LocalDebit_bound (N Q L : Nat) (T S : Tree) (q : Nat)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) (budget : q≤Q)
 (tlabs : ∀x,x∈leaves T→x<2^L) (slabs : ∀x,x∈leaves S→x<2^L) :
 (closedRule5LocalDebit T S q:Rat)≤(C5 N Q L:Rat)*Rule5ActualTrace.base^q := by
 have nonneg:0≤(C5 N Q L:Rat)*Rule5ActualTrace.base^q:=
  Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))
 unfold closedRule5LocalDebit
 simp only [hp,ite_true]
 cases pre:DepthOne.pretest01 T S with
 | refused=>simpa only [Rat.natCast_ofNat] using nonneg
 | found e=>simpa only [Rat.natCast_ofNat] using nonneg
 | rejected=>cases he:early T S with
  | hard2 c d=>
   dsimp only
   have sound:=early_sound T S;rw [he] at sound
   cases route:(hard2FrontMeter T S c q).value with
   | refused=>simpa only [route,Rat.natCast_ofNat] using nonneg
   | direct answer=>simpa only [route,Rat.natCast_ofNat] using nonneg
   | disjointPaid=>simpa only [route,Rat.natCast_ofNat] using nonneg
   | paid out=>simpa only [route,Rat.natCast_ofNat] using nonneg
   | admittedRule5=>
    simpa only [Rule5ActualTrace.base] using admitted_route_bound q N Q L hp sound.1 sound.2.1
     sound.2.2.1 sound.2.2.2 route ⟨size,budget,tlabs,slabs⟩
  | common reverse c=>simpa only [Rat.natCast_ofNat] using nonneg
  | one reverse c=>simpa only [Rat.natCast_ofNat] using nonneg
  | high reverse c=>simpa only [Rat.natCast_ofNat] using nonneg
  | rule4Forward s=>simpa only [Rat.natCast_ofNat] using nonneg
  | rule4Reverse s=>simpa only [Rat.natCast_ofNat] using nonneg
  | refused=>simpa only [Rat.natCast_ofNat] using nonneg
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/CommonBranchWork.lean:43
section
open OrdinaryDispatch.FullSourceWork
open OrdinaryDispatch
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open OrdinaryDispatch.FastOrdinary
theorem commonBranchMeter_local_bound (q : Nat) (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate)
 (hp : DepthOne.proper T S=true)
 (selected : CherryBranching.select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.common,c)) :
 (commonBranchMeter FastOrdinary.solve (fun _ _ _=>0) q T S reverse c).work≤
 256*(2*(leaves T).length+1)^2 := by
 let n:=(leaves T).length
 have same:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
 have t:=treeNodes_leafCount T;have s:=treeNodes_leafCount S
 have ready:=common_pair_ready hp selected
 have smaller:=common_pair_label_count hp selected
 have pn:=treeNodes_leafCount (commonPair T S reverse c).1
 have pair:=commonPairMeter_bound T S reverse c (2*n) (by dsimp [n];omega) (by dsimp [n];omega)
 have a:=leaves_meter_square (commonPair T S reverse c).1 (2*n) (by dsimp [n];omega)
 have b:=leaves_meter_square T (2*n) (by dsimp [n];omega)
 have pos:1≤(2*n+1)^2:=Nat.one_le_pow _ _ (by omega)
 simp only [commonBranchMeter,commonPairMeter_value,meterLeaves_value,ready.2,ite_true]
 cases answer:FastOrdinary.solve q (commonPair T S reverse c).1 (commonPair T S reverse c).2 with
 | none=>dsimp only;change _≤256*(2*n+1)^2;omega
 | some F=>
  have payload:=RebasedSourceCounter20261022.closed_payload (commonPair T S reverse c).1 (commonPair T S reverse c).2 q ready.1 answer
  have pay:Rule5LocalWork.cells F≤2*n:=by dsimp [n];omega
  have expand:=expandCommonMeter_bound T S reverse c F (2*n) (by dsimp [n];omega) (by dsimp [n];omega) pay
  dsimp only
  change _≤256*(2*n+1)^2
  omega
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/ClosedLocalSource.lean:21
section
open OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch
open RMAF ForestState Universal233 WholeSourceWork
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.EarlyLocalWork
theorem commonLocalDebit_bound (N : Nat) (T S : Tree) (q : Nat)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) :
 commonLocalDebit T S q≤commonCoefficient N := by
 have scale:=Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left (show 2*(leaves T).length+1≤2*N+1 by omega) 2)
 unfold commonLocalDebit
 simp only [hp,ite_true]
 cases pre:DepthOne.pretest01 T S with
 | refused=>exact Nat.zero_le _
 | found e=>exact Nat.zero_le _
 | rejected=>
  have sound:=early_sound T S
  cases he:early T S with
  | common reverse c=>
   rw [he] at sound
   exact Nat.le_trans (commonBranchMeter_local_bound q T S reverse c hp sound) scale
  | one reverse c=>exact Nat.zero_le _
  | high reverse c=>exact Nat.zero_le _
  | rule4Forward s=>exact Nat.zero_le _
  | rule4Reverse s=>exact Nat.zero_le _
  | hard2 c d=>exact Nat.zero_le _
  | refused=>exact Nat.zero_le _
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/ClosedLocalSource.lean:108
section
open OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch
open RMAF ForestState Universal233 WholeSourceWork
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.EarlyLocalWork
theorem closedLocalDebit_bound (N Q : Nat) (T S : Tree) (q : Nat)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) (budget : q≤Q) :
 (closedLocalDebit T S q:Rat)≤(closedLocalPolynomial N Q:Rat)*Rule5ActualTrace.base^q := by
 have p:=nat_local_exponential _ _ q (prefix_local_cap q T S N hp size)
 have c:=nat_local_exponential _ _ q (commonLocalDebit_bound N T S q hp size)
 have h:=simpleLocalDebit_bound N Q T S q hp size budget
 have hcap:=Rat.mul_le_mul_of_nonneg_right (simpleSourceCoefficient_le_nat N Q)
  (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))
 have h':=Rat.le_trans h hcap
 have r:=rule4LocalDebit_bound N Q T S q hp size budget
 have f:=nat_local_exponential _ _ q (hard2FrontLocalDebit_bound N T S q hp size)
 have total:=rat_add_bounds (rat_add_bounds (rat_add_bounds (rat_add_bounds p c) h') r) f
 simpa only [closedLocalDebit,closedLocalPolynomial,Rat.natCast_add,Rat.add_mul] using total
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/ExtendedTreeOptimizer.lean:15
section
open OrdinaryDispatch.ExtendedSourceAssembly
open OrdinaryDispatch
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open OrdinaryDispatch.WorkRecursion OrdinaryDispatch.WorkIntegration OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.RecoveryLocalWork
theorem extendedLocalDebit_bound (N Q : Nat) (T S : Tree) (q : Nat)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) (budget : q≤Q) :
 (extendedLocalDebit T S q:Rat)≤(extendedLocalPolynomial N Q:Rat)*Rule5ActualTrace.base^q := by
 have sum:=rat_add_bounds (closedLocalDebit_bound N Q T S q hp size budget)
  (hardPaidLocalDebit_bound N Q T S q hp size budget)
 simpa only [extendedLocalDebit,extendedLocalPolynomial,Rat.natCast_add,Rat.add_mul] using sum
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/ReachLocalAssembly.lean:17
section
open OrdinaryDispatch.GoodPairGlobalAssembly
open OrdinaryDispatch
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open OrdinaryDispatch.WorkRecursion OrdinaryDispatch.WorkIntegration OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.ExtendedSourceAssembly OrdinaryDispatch.GlobalNumeric Universal233.Rule5ClosedSource
theorem joinedLocalSourceDebit_reachable_bound (q0 N Q L : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N) (initialBudget : q0≤Q)
 (labels0 : ∀x,x∈leaves T0++leaves S0→x<2^L)
 (d : Nat) (T S : Tree) (q : Nat) (path : Reach FastOrdinary.solve q0 T0 S0 d T S q) :
 (joinedLocalSourceDebit T S q:Rat)≤(joinedLocalPolynomial N Q L:Rat)*Rule5ActualTrace.base^q := by
 have domain:=reachableRule5InputDomain q0 N Q L T0 S0 hp0 size0 initialBudget labels0 path
 have cap0 : PairCap (2^L) T0 S0:=
  ⟨fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_left _ hx)),
   fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_right _ hx))⟩
 have hp:DepthOne.proper T S=true:=
  (reachable_invariant FastOrdinary.solve q0 N (2^L) T0 S0 hp0 size0 cap0 path).1
 have e:=extendedLocalDebit_bound N Q T S q hp domain.size domain.budget
 have g:=goodPairLocalDebit_bound N Q T S q hp domain.size domain.budget
 have f:=closedRule5LocalDebit_bound N Q (semanticWidth N L Q) T S q hp domain.size domain.budget
  domain.targetLabels domain.sourceLabels
 have sum:=rat_add_bounds (rat_add_bounds e g) f
 simpa only [joinedLocalSourceDebit,joinedLocalPolynomial,Rat.natCast_add,Rat.add_mul] using sum
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/OuterLocalAssembly.lean:57
section
open OrdinaryDispatch.OuterSource
open OrdinaryDispatch
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.GoodPairGlobalAssembly OrdinaryDispatch.GlobalNumeric
open OrdinaryDispatch.ExtendedSourceAssembly OrdinaryDispatch.GlobalSourceAssembly
theorem outerJoinedLocalDebit_reachable_bound (q0 N Q L : Nat) (T0 S0 : Tree)
 (hp0:DepthOne.proper T0 S0=true) (size0:(leaves T0).length≤N) (initialBudget:q0≤Q)
 (labels0:∀x,x∈leaves T0++leaves S0→x<2^L)
 (d : Nat) (T S : Tree) (q : Nat) (path:Reach FastOrdinary.solve q0 T0 S0 d T S q) :
 (outerJoinedLocalDebit T S q:Rat)≤(outerJoinedPolynomial N Q L:Rat)*Rule5ActualTrace.base^q := by
 have domain:=reachableRule5InputDomain q0 N Q L T0 S0 hp0 size0 initialBudget labels0 path
 have cap0:PairCap (2^L) T0 S0:=
  ⟨fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_left _ hx)),
   fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_right _ hx))⟩
 have hp:DepthOne.proper T S=true:=
  (reachable_invariant FastOrdinary.solve q0 N (2^L) T0 S0 hp0 size0 cap0 path).1
 have old:=joinedLocalSourceDebit_reachable_bound q0 N Q L T0 S0 hp0 size0 initialBudget labels0 d T S q path
 have new:=outerLocalDebit_bound N Q T S q hp domain.size domain.budget
 simpa only [outerJoinedLocalDebit,outerJoinedPolynomial,Rat.natCast_add,Rat.add_mul] using rat_add_bounds old new
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/CompleteWeightedSource.lean:64
section
open OrdinaryDispatch.CompleteSource
open OrdinaryDispatch
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.OuterSource
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.GoodPairGlobalAssembly OrdinaryDispatch.ExtendedSourceAssembly OrdinaryDispatch.GlobalNumeric
open OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.RecoveryLocalWork
theorem completeLocalDebit_reachable_bound (q0 N Q L : Nat) (T0 S0 : Tree)
 (hp0:DepthOne.proper T0 S0=true) (size0:(leaves T0).length≤N) (initialBudget:q0≤Q)
 (labels0:∀x,x∈leaves T0++leaves S0→x<2^L)
 (d : Nat) (T S : Tree) (q : Nat) (path:Reach FastOrdinary.solve q0 T0 S0 d T S q) :
 (completeLocalDebit T S q:Rat)≤(completeSourcePolynomial N Q L:Rat)*Rule5ActualTrace.base^q := by
 have domain:=reachableRule5InputDomain q0 N Q L T0 S0 hp0 size0 initialBudget labels0 path
 have cap0:PairCap (2^L) T0 S0:=
  ⟨fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_left _ hx)),
   fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_right _ hx))⟩
 have hp:DepthOne.proper T S=true:=
  (reachable_invariant FastOrdinary.solve q0 N (2^L) T0 S0 hp0 size0 cap0 path).1
 have old:=outerJoinedLocalDebit_reachable_bound q0 N Q L T0 S0 hp0 size0 initialBudget labels0 d T S q path
 have add:=missingLocalDebit_bound N Q T S q hp domain.size domain.budget
 rw [completeLocalDebit_decomposition q T S hp]
 simpa only [completeSourcePolynomial,Rat.natCast_add,Rat.add_mul] using rat_add_bounds old add
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/CompleteWeightedSource.lean:94
section
open OrdinaryDispatch.CompleteSource
open OrdinaryDispatch
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.OuterSource
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.GoodPairGlobalAssembly OrdinaryDispatch.ExtendedSourceAssembly OrdinaryDispatch.GlobalNumeric
open OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.RecoveryLocalWork
theorem completeSourceCounter_bound (q0 N Q L : Nat) (T0 S0 : Tree)
 (hp0:DepthOne.proper T0 S0=true) (size0:(leaves T0).length≤N) (initialBudget:q0≤Q)
 (labels0:∀x,x∈leaves T0++leaves S0→x<2^L) :
 (completeSourceCounter q0 T0 S0:Rat)≤(completeSourcePolynomial N Q L:Rat)*callNodeFactor*
 ((leaves T0).length+1:Nat)*Rule5ActualTrace.base^q0 := by
 exact sourceSubtotal_reach_bound completeLocalDebit q0 T0 S0 (completeSourcePolynomial N Q L) Rat.natCast_nonneg
  (completeLocalDebit_reachable_bound q0 N Q L T0 S0 hp0 size0 initialBudget labels0) hp0 Reach.root
end

-- Origin: /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/full_source_counter_assembly_20261017T111531Z/build/CompleteWeightedSource.lean:104
section
open OrdinaryDispatch.CompleteSource
open OrdinaryDispatch
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.OuterSource
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.GlobalSourceAssembly
open OrdinaryDispatch.GoodPairGlobalAssembly OrdinaryDispatch.ExtendedSourceAssembly OrdinaryDispatch.GlobalNumeric
open OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.RecoveryLocalWork
theorem completeSourceQuery_bound (T S : Tree) (L : Nat) (hp:DepthOne.proper T S=true)
 (labels:∀x,x∈leaves T++leaves S→x<2^L) (b : Nat) (budget:b<(leaves T).length) :
 (completeSourceCounter b T S:Rat)≤(completeQueryPolynomial (leaves T).length L:Rat)*(233/100:Rat)^b := by
 have h:=completeSourceCounter_bound b (leaves T).length (leaves T).length L T S hp (Nat.le_refl _) (Nat.le_of_lt budget) labels
 simpa only [completeSourceCounter,completeQueryPolynomial,Rat.natCast_mul,Rat.natCast_ofNat,callNodeFactor,Rule5ActualTrace.base] using h
end

#print axioms completeSourceCounter_bound
#print axioms completeSourceQuery_bound
end RebasedSourceCounter20261022
