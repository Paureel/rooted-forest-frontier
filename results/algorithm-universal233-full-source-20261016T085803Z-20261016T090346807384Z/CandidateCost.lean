import BlockCost
namespace AllGoodDP.LocalWork
open RMAF ForestState Universal233.WholeSourceWork Universal233.CoreWork

def meterCandidate (T : Option Tree) (ss : List Tree) : Charged (List (List Nat)) :=
 match T with
 | none => ⟨[],4⟩
 | some t =>
  let p := meterSolve (List.range ss.length) (fun x=>meterOwner x ss) t
  let b := meterBlocks p.value
  ⟨b.value,p.work+b.work+4*(ss.length+1)+8⟩
@[simp] theorem meterCandidate_value (T : Option Tree) (ss : List Tree) :
 (meterCandidate T ss).value=candidate T ss := by
 cases T <;> simp [meterCandidate,candidate]

def candidatePolynomial (n : Nat) : Nat :=
 solveBill (2*n*ownerRowCap (2*n)+4) (2*n) (2*n)+blocksBill (2*n)+4*(2*n+1)+8

theorem actual_candidate_work (t : Tree) (ss : List Tree) (hp : proper (some t) ss=true) :
 (meterCandidate (some t) ss).work≤candidatePolynomial (leaves t).length := by
 let n := (leaves t).length
 have volume := GenericForest.LocalPolynomial.state_size_bounds (some t) ss hp n (Nat.le_refl _)
 have ht : treeNodes t≤2*n := volume.1
 have hs := volume.2.2
 have source : ∀s,s∈ss→treeNodes s≤2*n := fun s hm=>(GenericForest.LocalPolynomial.source_size_bounds (some t) ss hp n (Nat.le_refl _) s hm).1
 have ownerwork : ∀x,x∈leaves t→(meterOwner x ss).work≤2*n*ownerRowCap (2*n)+4 := by
  intro x _
  have h := meterOwner_work x ss (2*n) source
  have mul := Nat.mul_le_mul_right (ownerRowCap (2*n)) hs
  omega
 have nonempty : List.range ss.length≠[] := by
  have ne := some_sources_nonempty t ss hp
  simp only [ne_eq,List.range_eq_nil,List.length_eq_zero_iff]
  exact ne
 have paint := meterSolve_work (List.range ss.length) (fun x=>meterOwner x ss) t nonempty _ (2*n) ht ownerwork
 simp only [List.length_range] at paint
 have raise := solveBill_mono (Nat.le_refl (2*n*ownerRowCap (2*n)+4)) hs (Nat.le_refl (2*n))
 have bounds : paintNodes (meterSolve (List.range ss.length) (fun x=>meterOwner x ss) t).value≤2*n := by
  rw [paintNodes_erase,meterSolve_erase _ _ _ nonempty]
  exact ht
 have block := meterBlocks_work _ (2*n) bounds
 simp only [meterCandidate,candidatePolynomial]
 dsimp only [n] at paint raise block hs
 omega

inductive PaintScalars (labelCap colorCap : Nat) : Paint→Prop where
 | leaf {x c : Nat} (label : x<labelCap) (color : c<colorCap) : PaintScalars labelCap colorCap (.leaf x c)
 | node {c : Nat} {l r : Paint} (color : c<colorCap) (left : PaintScalars labelCap colorCap l)
   (right : PaintScalars labelCap colorCap r) : PaintScalars labelCap colorCap (.node c l r)

theorem valid_scalars {cs : List Nat} {owner : Nat→Nat} {t : Tree} {p : Paint}
 (h : Valid cs owner t p) (L M : Nat) (labels : ∀x,x∈leaves t→x<L) (colors : ∀c,c∈cs→c<M) : PaintScalars L M p := by
 induction h with
 | leaf x hc => exact .leaf (labels x (by simp [leaves])) (colors _ hc)
 | @node t u p q c hc hp hq il ir =>
  exact .node (colors _ hc) (il (fun x hx=>labels x (by simp [leaves,hx]))) (ir (fun x hx=>labels x (by simp [leaves,hx])))

theorem actual_paint_scalars (t : Tree) (ss : List Tree) (hp : proper (some t) ss=true)
 (L : Nat) (labels : ∀x,x∈leaves t→x<L) :
 PaintScalars L ss.length (meterSolve (List.range ss.length) (fun x=>meterOwner x ss) t).value := by
 rw [meterSolve_value]
 simp only [meterOwner_value]
 exact valid_scalars (actual_paint_spec t ss hp).1 L ss.length labels (fun c hc=>List.mem_range.1 hc)
end AllGoodDP.LocalWork
