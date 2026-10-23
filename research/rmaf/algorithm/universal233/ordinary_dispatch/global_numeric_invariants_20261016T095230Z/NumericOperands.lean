import NumericSourceBinding
namespace OrdinaryDispatch.GlobalNumeric
open RMAF ForestState Universal233 Universal233.CoreWork
open GenericForest.CheckCorrespondence GenericForest.LocalPolynomial

theorem forest_branch_operands (t : Tree) (ss : List Tree) (h : GenericForest.Overlap) (q N Q : Nat)
 (hp : proper (some t) ss=true) (size : (leaves t).length≤N) (budget : q≤Q)
 (io : Nat×Universal233.CoreProgram.Output) (mem : io∈GenericForest.branches t ss h q) :
 io.1<2*N ∧ io.2.sourceCuts.length≤Q ∧
 (∀v,v∈io.2.sourceCuts→v.length≤2*N) ∧ (io.2.sourceCuts.map List.length).sum≤Q*(2*N) := by
 obtain ⟨s,index,generated⟩:=branch_generated t ss h q io mem
 have source:=source_size_bounds (some t) ss hp N size s (List.mem_of_getElem? index)
 have valid:=CutRealization.generate_original_realization s (VertexGeometry.colorLabel t h.vertex) q io.2 generated
 have cutcount:=SourceCoverage.generate_output_budget s (VertexGeometry.colorLabel t h.vertex) q io.2 generated
 have state:=state_size_bounds (some t) ss hp N size
 have idx : io.1<ss.length := by
  by_cases good : io.1<ss.length
  · exact good
  · have absent : ss[io.1]?=none := List.getElem?_eq_none_iff.2 (by omega)
    rw [absent] at index
    contradiction
 have address : ∀v,v∈io.2.sourceCuts→v.length≤2*N :=
  fun v hv=>Nat.le_trans (valid_address_bound s v (valid.2.1 v hv)) source.1
 have sum:=nat_sum_le_constant io.2.sourceCuts List.length (2*N) address
 exact ⟨by omega,by omega,address,Nat.le_trans sum (Nat.mul_le_mul_right (2*N) (by omega))⟩

/-- Semantic scalar operands bounded by a polynomial have polynomial bitwidth.
No assertion about the physical length of a padded binary list follows. -/
theorem scalar_bits_of_cap (x P : Nat) (cap : x≤P) : labelBits x≤P+2 := by
 have power:=add_lt_power 0 P
 simp only [Nat.pow_zero,Nat.zero_add] at power
 have exp:2^(P+1)≤2^(P+2):=Nat.pow_le_pow_right (by decide) (by omega)
 exact labelBits_of_lt (by omega) (by omega)

def structuralOperandCap (N Q : Nat) : Nat := 8*(N+Q+1)^2

theorem ordinary_scalar_cap (N Q : Nat) : 2*N+2*Q+3≤structuralOperandCap N Q := by
 have e:1≤N+Q+1:=by omega
 have sq : N+Q+1≤(N+Q+1)^2 := by
  have h:=Nat.mul_le_mul_left (N+Q+1) e
  simpa only [Nat.mul_one,Nat.pow_two] using h
 unfold structuralOperandCap
 omega

/-- Arithmetic interface for the separate represented producer: after proving
stored label widths <= semanticWidth and budget storage <=Q+1, use node cap2N
in the pinned caller's width expression L'+Q+2*N'+3. -/
def representedCapacityEnvelope (N L Q : Nat) : Nat := L+3*Q+6*N+6

theorem represented_capacity_arithmetic (N L Q : Nat) :
 semanticWidth N L Q+Q+2*(2*N)+3=representedCapacityEnvelope N L Q := by
 unfold semanticWidth representedCapacityEnvelope
 omega
end OrdinaryDispatch.GlobalNumeric
