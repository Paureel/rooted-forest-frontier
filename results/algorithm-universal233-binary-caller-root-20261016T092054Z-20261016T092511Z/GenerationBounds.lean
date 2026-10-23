import PolyBounds
namespace GenericForest.LocalPolynomial
open RMAF ForestState Universal233 Universal233.CoreWork Universal233.CoreProgram Universal233.WholeSourceWork

theorem color_cap_bound (t : Tree) (v : RMAF.Vertex) (M : Nat)
 (nodes : treeNodes t≤2*M) (address : v.length≤M) : colorCap t v≤colorBound M := by
 have product:=Nat.mul_le_mul (Nat.add_le_add_right nodes 3) nodes
 have scaled:=Nat.mul_le_mul_left 16 product
 have addr:=Nat.mul_le_mul_left 4 (Nat.add_le_add_right address 1)
 unfold colorCap colorBound
 simp only [Nat.mul_assoc] at scaled ⊢
 omega

theorem generation_bill_bound (t : Tree) (ss : List Tree) (q M i : Nat) (s : Tree) (v : RMAF.Vertex)
 (hp : proper (some t) ss=true) (size : (leaves t).length≤M) (budget : q≤M)
 (hi : ss[i]?=some s) (address : v.length≤M) : generationBill t ss i v q≤generationCap M*2^q := by
 have hm:=List.mem_of_getElem? hi
 have source:=source_size_bounds (some t) ss hp M size s hm
 have target:=(state_size_bounds (some t) ss hp M size).1
 have gen:=generate_prefix_bound s (VertexGeometry.colorLabel t v) q M source.1 budget
 have colors : ((leaves s).map fun x=>(meterColorLabel t v x).work).sum≤M*colorBound M := by
  have sum:=nat_sum_le_constant (leaves s) (fun x=>(meterColorLabel t v x).work) (colorBound M)
   (fun x _=>Nat.le_trans (meterColorLabel_bound t v x) (color_cap_bound t v M target address))
  exact Nat.le_trans sum (Nat.mul_le_mul_right (colorBound M) source.2)
 have pow : 1≤2^q:=Nat.pow_pos (by decide)
 have scaled:=Nat.mul_le_mul_left (M*colorBound M) pow
 simp only [Nat.mul_one] at scaled
 simp only [generationBill,hi,generationCap,Nat.add_mul]
 omega

theorem minimal_bill_bound (D : List Nat) (t : Tree) (M : Nat)
 (labels : D.length≤M) (nodes : treeNodes t≤2*M) : (meterMinimal D t).work≤spanBound M := by
 have actual:=meterMinimal_bound D t (treeNodes t) (Nat.le_refl _)
 have inside : D.length+treeNodes t+2≤3*M+2:=by omega
 have factor:=Nat.add_le_add_right (Nat.mul_le_mul_left 16 inside) 16
 have caple:=Nat.mul_le_mul factor (Nat.add_le_add_right nodes 1)
 have final:=Nat.mul_le_mul caple nodes
 exact Nat.le_trans actual final

theorem overlap_bill_bound (t : Tree) (ss : List Tree) (M : Nat)
 (hp : proper (some t) ss=true) (size : (leaves t).length≤M) : overlapBill t ss≤overlapCap M := by
 have volume:=state_size_bounds (some t) ss hp M size
 have target : treeNodes t≤2*M:=volume.1
 let pairBound:=2*spanBound M+16*(2*M+1)^3
 have pair (a b : Tree) (ha : a∈ss) (hb : b∈ss) :
  (meterMinimal (leaves a) t).work+(meterMinimal (leaves b) t).work+16*(treeNodes t+1)^3≤pairBound := by
  have aw:=minimal_bill_bound (leaves a) t M (source_size_bounds (some t) ss hp M size a ha).2 volume.1
  have bw:=minimal_bill_bound (leaves b) t M (source_size_bounds (some t) ss hp M size b hb).2 volume.1
  have extra:=Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right target 1) 3)
  dsimp [pairBound];omega
 have outer:=nat_sum_le_constant ss (fun a=>(ss.map fun b=>
  (meterMinimal (leaves a) t).work+(meterMinimal (leaves b) t).work+16*(treeNodes t+1)^3).sum)
  (ss.length*pairBound) (fun a ha=>nat_sum_le_constant ss _ pairBound (fun b hb=>pair a b ha hb))
 have sizes:=Nat.mul_le_mul volume.2.2 volume.2.2
 have final:=Nat.mul_le_mul_right pairBound sizes
 have eq : ss.length*(ss.length*pairBound)=(ss.length*ss.length)*pairBound:=by ac_rfl
 rw [eq] at outer
 exact Nat.le_trans outer final

theorem generate_output_count (s : Tree) (color : Nat → Nat) (q : Nat) :
 (generate s color q).outputs.length≤6*2^q := by
 unfold generate
 split
 · have records:=run_records_bound (min q ((leaves s).length-1)) (fromTree color [] s) [] []
   have power : 2^(min q ((leaves s).length-1)+1)≤2*2^q := by
    have h:=Nat.pow_le_pow_right (n:=2) (by decide) (Nat.add_le_add_right (Nat.min_le_left q ((leaves s).length-1)) 1)
    simpa only [Nat.pow_succ,Nat.mul_comm] using h
   have scaled:=Nat.mul_le_mul_left 3 power
   simp only [CoreWork.records] at records
   omega
 · simp

theorem raw_output_count (t : Tree) (ss : List Tree) (i : Nat) (v : RMAF.Vertex) (q : Nat) :
 (raw t ss i v q).length≤6*2^q := by
 unfold raw
 split
 · simp
 · exact generate_output_count _ _ _

theorem branches_output_count (t : Tree) (ss : List Tree) (h : Overlap) (q : Nat) :
 (branches t ss h q).length≤12*2^q := by
 have a:=raw_output_count t ss h.left h.vertex q
 have b:=raw_output_count t ss h.right h.vertex q
 simp only [branches,List.length_append,List.length_map]
 omega
end GenericForest.LocalPolynomial
