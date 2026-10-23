import LiteralColors
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedHard2Survival

theorem selected_mono_own (D E : List Nat) (sub : D⊆E) (T : Tree) :
 ∀v,selectedLeaves D T v→selectedLeaves E T v := by
 induction T with
 | leaf x => intro v h;exact ⟨h.1,sub h.2⟩
 | node l r ihl ihr =>
  intro v h
  cases v with
  | nil => exact False.elim h
  | cons b v =>
   cases b
   · exact ihl v h
   · exact ihr v h

theorem agreement_block_labels (T S : Tree) (F : List (List Nat)) (agree : agreement T S F=true) :
 ∀K,K∈F→∀x,x∈K→x∈leaves T := by
 have checks:=agree
 simp only [agreement,Bool.and_eq_true] at checks
 have part:=checks.1.1.1.1
 simp only [partitionCheck,Bool.and_eq_true] at part
 intro K kF x hx
 exact List.contains_iff_mem.mp (List.all_eq_true.mp part.2 x (List.mem_flatten.mpr ⟨K,kF,hx⟩))

def ParentMono (F : List (List Nat)) (A : List Nat) (color : Nat→Nat) : Prop :=
 ∀K,K∈F→K⊆A→LabelMonochromatic color K

theorem avoidance_monochrome (T S : Tree) (F : List (List Nat)) (A : List Nat) (v : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (agree : agreement T S F=true)
 (nonlabel : ¬selectedLeaves (leaves T) T v) (avoid : ParentAvoids T F A v) :
 ParentMono F A (colorLabel T v) := by
 intro K kF sub
 have labels:=agreement_block_labels T S F agree K kF
 have no : ¬selectedLeaves K T v := fun h=>nonlabel (selected_mono_own K (leaves T) labels T v h)
 exact (original_label_avoids_iff T K v (IndependentReconstruction.proper_parts proper).1 labels no).mp (avoid K kF sub)

theorem constant_monochrome (F : List (List Nat)) (A : List Nat) : ParentMono F A (fun _=>0) := by
 intro K _ _ x y _ _;rfl

theorem joint_monochrome (T : Tree) (F : List (List Nat)) (A : List Nat) (v w : RMAF.Vertex)
 (a : ParentMono F A (colorLabel T v)) (b : ParentMono F A (colorLabel T w)) :
 ParentMono F A (jointLabel T v w) := by
 intro K kF sub x y hx hy
 unfold jointLabel
 rw [a K kF sub x y hx hy,b K kF sub x y hx hy]

theorem tagged_monochrome (F : List (List Nat)) (A B C : List Nat) (ca cb cc : Nat→Nat)
 (ref : VertexGeometry.Refines F [A,B,C])
 (ab : ∀x,x∈A→x∈B→False) (ac : ∀x,x∈A→x∈C→False) (bc : ∀x,x∈B→x∈C→False)
 (ma : ParentMono F A ca) (mb : ParentMono F B cb) (mc : ParentMono F C cc) :
 ∀K,K∈F→LabelMonochromatic (taggedColor A B ca cb cc) K := by
 intro K kF
 obtain ⟨D,dP,sub⟩:=ref K kF
 simp only [List.mem_cons,List.not_mem_nil,or_false] at dP
 rcases dP with eq|eq|eq <;> subst D
 · intro x y hx hy
   simp only [taggedColor,ite_eq_left (sub x hx),ite_eq_left (sub y hy)]
   rw [ma K kF sub x y hx hy]
 · intro x y hx hy
   have nx : x∉A := fun h=>ab x h (sub x hx)
   have ny : y∉A := fun h=>ab y h (sub y hy)
   simp only [taggedColor,ite_eq_right nx,ite_eq_right ny,ite_eq_left (sub x hx),ite_eq_left (sub y hy)]
   rw [mb K kF sub x y hx hy]
 · intro x y hx hy
   have nxa : x∉A := fun h=>ac x h (sub x hx)
   have nya : y∉A := fun h=>ac y h (sub y hy)
   have nxb : x∉B := fun h=>bc x h (sub x hx)
   have nyb : y∉B := fun h=>bc y h (sub y hy)
   simp only [taggedColor,ite_eq_right nxa,ite_eq_right nya,ite_eq_right nxb,ite_eq_right nyb]
   rw [mc K kF sub x y hx hy]
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.selected_mono_own
#print axioms ContactedHard2Survival.selected_mono_own
#check @ContactedHard2Survival.agreement_block_labels
#print axioms ContactedHard2Survival.agreement_block_labels
#check @ContactedHard2Survival.avoidance_monochrome
#print axioms ContactedHard2Survival.avoidance_monochrome
#check @ContactedHard2Survival.constant_monochrome
#print axioms ContactedHard2Survival.constant_monochrome
#check @ContactedHard2Survival.joint_monochrome
#print axioms ContactedHard2Survival.joint_monochrome
#check @ContactedHard2Survival.tagged_monochrome
#print axioms ContactedHard2Survival.tagged_monochrome
