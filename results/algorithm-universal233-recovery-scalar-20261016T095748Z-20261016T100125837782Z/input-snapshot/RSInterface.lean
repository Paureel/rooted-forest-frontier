import RSCopy
namespace OrdinaryDispatch.RecoveryScalar
open RMAF Universal233 CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryLocalWork

def TreeAddresses (N : Nat) : GTree→Prop
 | .leaf g=>g.origin.length≤N
 | .node p l r=>p.length≤N ∧ TreeAddresses N l ∧ TreeAddresses N r

theorem tree_address_cap (N : Nat) (t : GTree) (h : footprint t≤N) : TreeAddresses N t := by
 induction t with
 | leaf g=>simp only [footprint] at h;dsimp only [TreeAddresses];omega
 | node p l r il ir=>
  have hl:footprint l≤N:=by simp only [footprint] at h;omega
  have hr:footprint r≤N:=by simp only [footprint] at h;omega
  exact ⟨by simp only [footprint] at h;omega,il hl,ir hr⟩

theorem input_resource_polynomial (t : Tree) : inputResource t≤(treeNodes t+2)^2 := by
 simp only [inputResource,Nat.pow_two,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
 omega

theorem receipt_field_caps (q Q : Nat) (hq : q≤Q) (t d c) :
 let r:=run q t d c
 r.outputs.length<2^(Q+5) ∧ r.refusals.length<2^(Q+5) ∧
 r.visited<2^(Q+5) ∧ r.childAttempts<2^(Q+5) ∧ r.pruned<2^(Q+5) := by
 have h:=run_counter_width q Q hq t d c
 dsimp only [eventSize,records] at h
 dsimp only
 omega

theorem output_length_width (N L Q : Nat) (o : Output) (h : OutputCap N (2^L) o) :
 o.partition.flatten.length<2^(scalarWidth N L Q) := by
 have cells:=output_flatten_cap N (2^L) o h
 have b:N+1≤2^labelBits (N+1):=Nat.le_of_lt (Nat.lt_log2_self (n:=N+1))
 have a:N≤2^labelBits (N+1):=by omega
 have p:=Nat.mul_le_mul a b
 have eq:(2^labelBits (N+1))*(2^labelBits (N+1))=2^(2*labelBits (N+1)):=by
  rw [←Nat.pow_add];congr 1;omega
 rw [eq] at p
 have exp:2*labelBits (N+1)+1≤scalarWidth N L Q:=by unfold scalarWidth;omega
 have grow:=Nat.pow_le_pow_right (n:=2) (by decide : 0<2) exp
 have positive:0<2^(2*labelBits (N+1)):=Nat.pow_pos (by decide)
 rw [Nat.pow_succ] at grow
 omega

/-- All initial/recursive recovery payload ranges derive from the actual source.
The supplied original label cap remains explicit. No bit runtime is asserted. -/
theorem final_recovery_ranges (t : Tree) (P : List (List Nat)) (L : Nat)
 (hn : (leaves t).Nodup) (hp : partitionCheck (leaves t) P=true)
 (labels : ∀x∈leaves t,x<2^L) :
 (∀q current d c,Descendant t (FinalCutRecovery.blockColor P) (P.length-1) q current d c→
  StateCap (inputResource t) (2^L) q current d c) ∧
 (∀o∈(generate t (FinalCutRecovery.blockColor P) (P.length-1)).outputs,
  OutputCap (inputResource t) (2^L) o) := by
 have colors:=checked_color_caps t P L hn hp labels
 exact ⟨by intro q current d c reach;exact descendant_caps t _ _ _ labels (by intro x _;exact colors x) reach,
  generate_output_caps t _ _ _ labels (by intro x _;exact colors x)⟩

/-- The old source coefficient64 and exponential prefix factor are preserved.
This conjunction adds range facts; it does not multiply source work by an
unimplemented whole-program scalar fee. -/
theorem source_bound_and_ranges (t : Tree) (P : List (List Nat)) (L : Nat)
 (hn : (leaves t).Nodup) (hp : partitionCheck (leaves t) P=true)
 (he : pairwiseEmbeddings t P=true) (labels : ∀x∈leaves t,x<2^L) :
 (OrdinaryDispatch.RecoveryLocalWork.meterRecover t P).work≤
  recoverySourceEnvelope (leaves t).length*2^(P.length-1) ∧
 (∀o∈(generate t (FinalCutRecovery.blockColor P) (P.length-1)).outputs,
  OutputCap (inputResource t) (2^L) o) :=
 ⟨final_source_uniform t P hn hp he,(final_recovery_ranges t P L hn hp labels).2⟩

/-- A concrete finite-bit family on supplied arrays. These are local primitives,
not a provider for unimplemented represented recovery control flow. -/
theorem finite_primitive_work (W : Nat) (xs ys : List Bool)
 (xl : xs.length≤W) (yl : ys.length≤W) :
 (copiedEqual xs ys).work≤128*(W+1) ∧
 (leBits xs ys).work≤128*(W+1) ∧
 (minBits xs ys).work≤128*(W+1) ∧
 (subtractBits xs ys).work≤128*(W+1) ∧
 (counterAdd W xs ys).work≤128*(W+1) := by
 have a:=copiedEqual_work W xs ys xl yl
 have b:=(scalar_width_bounds W xs ys xl yl).2.1
 have c:=minBits_work W xs ys xl yl
 have d:=(scalar_width_bounds W xs ys xl yl).2.2.2
 have e:=counterAdd_work W xs ys xl yl
 omega
end OrdinaryDispatch.RecoveryScalar
