import NumericStep
namespace OrdinaryDispatch.GlobalNumeric
open RMAF ForestState Universal233
open OrdinaryDispatch.WorkRecursion OrdinaryDispatch.FastOrdinary

/-- Reachability is over the exact source trace, with no success, uniqueness,
q<=current-size or rho assumption. Every literal duplicate occurrence satisfies
this relation; it is a reachability relation, not a call-count quotient. -/
inductive Reach (rec : Nat→Tree→Tree→Option CommonForest) (Q : Nat) (T0 S0 : Tree) :
 Nat→Tree→Tree→Nat→Prop where
 | root : Reach rec Q T0 S0 0 T0 S0 Q
 | next {d T S q p r} : Reach rec Q T0 S0 d T S q →
   (p,r)∈(ordinaryStepTrace rec q T S).queries → Reach rec Q T0 S0 (d+1) p.1 p.2 r

/-- Original-input invariant derived at every literal source edge. -/
theorem reachable_invariant (rec : Nat→Tree→Tree→Option CommonForest) (Q N M : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N) (cap0 : PairCap M T0 S0)
 {d T S q} (reach : Reach rec Q T0 S0 d T S q) :
 DepthOne.proper T S=true ∧ q≤Q ∧ (leaves T).length≤N ∧ (leaves S).length≤N ∧
 d+q+(leaves T).length≤Q+N ∧ PairCap (M+2*d) T S := by
 induction reach with
 | root =>
  have same:=((DepthOne.proper_iff T0 S0).1 hp0).2.2.length_eq
  exact ⟨hp0,Nat.le_refl _,size0,by omega,by omega,by simpa using cap0⟩
 | @next d T S q p r path mem ih =>
  have bounds:=ordinaryStepTrace_bounds rec q ih.1 p r mem
  have numeric:=ordinaryStepTrace_cap rec q ih.1 (M+2*d) ih.2.2.2.2.2 p r mem
  have decrease : r+(leaves p.1).length<q+(leaves T).length := by
   have strict:=bounds.2.2.2.2
   omega
  refine ⟨bounds.2.1,by omega,by omega,by omega,by omega,?_⟩
  simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using numeric

theorem reachable_path_depth (rec : Nat→Tree→Tree→Option CommonForest) (Q N M : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N) (cap0 : PairCap M T0 S0)
 {d T S q} (reach : Reach rec Q T0 S0 d T S q) : d≤Q+N := by
 have h:=reachable_invariant rec Q N M T0 S0 hp0 size0 cap0 reach
 omega

theorem reachable_uniform_cap (rec : Nat→Tree→Tree→Option CommonForest) (Q N M : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N) (cap0 : PairCap M T0 S0)
 {d T S q} (reach : Reach rec Q T0 S0 d T S q) : PairCap (M+2*(Q+N)) T S := by
 have h:=reachable_invariant rec Q N M T0 S0 hp0 size0 cap0 reach
 have depth : d≤Q+N := by omega
 exact ⟨treeCap_mono h.2.2.2.2.2.1 (by omega),treeCap_mono h.2.2.2.2.2.2 (by omega)⟩

theorem add_lt_power (L t : Nat) : 2^L+t<2^(L+t+1) := by
 have positive : 0<2^L := Nat.pow_pos (by decide)
 induction t with
 | zero => simp only [Nat.add_zero,Nat.pow_succ];omega
 | succ t ih =>
  have eq : L+(t+1)+1=(L+t+1)+1 := by omega
  rw [eq,Nat.pow_succ]
  omega

/-- Deliberately conservative polynomial semantic bitwidth in original input
label bits L, original leaf cap N and original budget Q. -/
def semanticWidth (N L Q : Nat) : Nat := L+2*(Q+N)+3

theorem reachable_label_bits (rec : Nat→Tree→Tree→Option CommonForest) (Q N L : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N)
 (labels0 : ∀x,x∈leaves T0++leaves S0→x<2^L)
 {d T S q} (reach : Reach rec Q T0 S0 d T S q) :
 ∀x,x∈leaves T++leaves S→x<2^(semanticWidth N L Q) := by
 have cap0 : PairCap (2^L) T0 S0 :=
  ⟨fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_left _ hx)),
   fun x hx=>Nat.le_of_lt (labels0 x (List.mem_append_right _ hx))⟩
 have bound:=reachable_uniform_cap rec Q N (2^L) T0 S0 hp0 size0 cap0 reach
 have numeric:=add_lt_power L (2*(Q+N)+2)
 intro x hx
 have val : x≤2^L+2*(Q+N) := by
  rcases List.mem_append.1 hx with h|h
  · exact bound.1 x h
  · exact bound.2 x h
 have exponent : L+(2*(Q+N)+2)+1=semanticWidth N L Q := by unfold semanticWidth;omega
 rw [exponent] at numeric
 omega

/-- Extra local builder markers are also bounded before refusal or callbacks.
Their creation does not mutate the ordinary state, and only paid jobs enter Reach. -/
theorem reachable_builder_fresh (rec : Nat→Tree→Tree→Option CommonForest) (Q N M : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N) (cap0 : PairCap M T0 S0)
 {d T S q} (reach : Reach rec Q T0 S0 d T S q) :
 OrdinaryCommonSplit.Source.labelMax (leaves T++leaves S)+2≤M+2*(Q+N)+2 := by
 have bound:=reachable_uniform_cap rec Q N M T0 S0 hp0 size0 cap0 reach
 have max:=pair_max_le bound
 omega
end OrdinaryDispatch.GlobalNumeric
