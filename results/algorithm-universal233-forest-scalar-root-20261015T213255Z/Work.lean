import CoreInvariants

/-! Problem-specific source work envelope for the immutable CoreProgram.
The receipt evaluator follows the exact source guards. A local charge accounts
for source traversals; outer receipt append copies and overbudget continuations
are additionally charged by their actual list lengths/call counts. Arbitrary
color-oracle evaluation is an external bill, never a unit-cost assumption. -/
namespace Universal233.CoreWork
open RMAF CoreProgram

/-- Constructor/list-cell footprint, excluding scalar Nat bit encodings. -/
def footprint : GTree → Nat
  | .leaf g => 1 + g.labels.length + g.origin.length
  | .node p l r => 1 + p.length + footprint l + footprint r

theorem footprint_pos (t : GTree) : 1 ≤ footprint t := by
  cases t <;> simp only [footprint] <;> omega

theorem normalize_footprint (t : GTree) : footprint (normalize t) ≤ footprint t := by
  induction t with
  | leaf g => exact Nat.le_refl _
  | node p l r ihl ihr =>
    cases hl : normalize l with
    | leaf a =>
      cases hr : normalize r with
      | leaf b =>
        simp only [normalize,hl,hr]
        split <;> simp_all only [footprint,List.length_append] <;> omega
      | node q a b => simp_all only [normalize,footprint]; omega
    | node q a b =>
      cases hr : normalize r <;> simp_all only [normalize,footprint] <;> omega

theorem erase_footprint (v : Vertex) (t u : GTree) (h : erase v t = some u) :
    footprint u ≤ footprint t := by
  induction t generalizing u with
  | leaf g =>
    simp only [erase] at h
    split at h
    · contradiction
    · cases h; exact Nat.le_refl _
  | node p l r ihl ihr =>
    simp only [erase] at h
    split at h
    · contradiction
    · cases hl : erase v l <;> cases hr : erase v r <;>
        simp only [hl,hr] at h
      · contradiction
      · cases h
        have hh := ihr _ hr
        simp only [footprint]; omega
      · cases h
        have hh := ihl _ hl
        simp only [footprint]; omega
      · cases h
        have hhl := ihl _ hl
        have hhr := ihr _ hr
        simp only [footprint]; omega

theorem groups_length (t : GTree) : (groups t).length ≤ footprint t := by
  induction t with
  | leaf g => simp only [groups,List.length_singleton,footprint]; omega
  | node p l r ihl ihr => simp only [groups,List.length_append,footprint]; omega

theorem group_size (t : GTree) (g : Group) (h : g ∈ groups t) :
    1 + g.labels.length + g.origin.length ≤ footprint t := by
  induction t with
  | leaf a => have he : g = a := by simpa [groups] using h
              subst g; exact Nat.le_refl _
  | node p l r ihl ihr =>
    simp only [groups,List.mem_append] at h
    rcases h with h | h
    · have hh := ihl h; simp only [footprint]; omega
    · have hh := ihr h; simp only [footprint]; omega

def treeNodes : Tree → Nat
  | .leaf _ => 1
  | .node l r => 1 + treeNodes l + treeNodes r

theorem treeNodes_pos (t : Tree) : 1 ≤ treeNodes t := by
  cases t <;> simp only [treeNodes] <;> omega

theorem treeNodes_le_twice_leaves (t : Tree) :
    treeNodes t + 1 = 2 * (leaves t).length := by
  induction t with
  | leaf x => rfl
  | node l r ihl ihr => simp only [treeNodes,leaves,List.length_append]; omega

theorem fromTree_footprint (color : Nat → Nat) (p : Vertex) (t : Tree) :
    footprint (fromTree color p t) ≤ treeNodes t * (p.length + treeNodes t + 2) := by
  induction t generalizing p with
  | leaf x => simp [fromTree,footprint,treeNodes]; omega
  | node l r ihl ihr =>
    have hl := ihl (p ++ [false])
    have hr := ihr (p ++ [true])
    have lp := treeNodes_pos l
    have rp := treeNodes_pos r
    simp only [List.length_append,List.length_singleton] at hl hr
    have hll : p.length + 1 + treeNodes l + 2 ≤ p.length + treeNodes (.node l r) + 2 := by
      simp only [treeNodes]; omega
    have hrr : p.length + 1 + treeNodes r + 2 ≤ p.length + treeNodes (.node l r) + 2 := by
      simp only [treeNodes]; omega
    have bl := Nat.le_trans hl (Nat.mul_le_mul_left (treeNodes l) hll)
    have br := Nat.le_trans hr (Nat.mul_le_mul_left (treeNodes r) hrr)
    have bp : 1 + p.length ≤ p.length + treeNodes (.node l r) + 2 := by
      simp only [treeNodes]; omega
    have hs := Nat.add_le_add (Nat.add_le_add bp bl) br
    simpa only [fromTree,footprint,treeNodes,Nat.add_mul,Nat.one_mul] using hs

/-- A source-local upper charge, not a claim about wall time. See COST-MODEL.md.
It includes both attempted-child guards/erase calls, all groups/find-filter/
normalization/output traversals, scalar counter operations and fixed control.
Receipt-list append cells and budget-pruned continuations are separate. -/
def localCharge (t : GTree) (d : List Group) (c : List Vertex) : Nat :=
  256 * (footprint t + d.length + c.length + 1)^3

def records (r : Receipt) : Nat := r.outputs.length + r.refusals.length

/-- Immutable-list append copies its left list; outputs are references here. -/
def appendCells (a : Receipt) : Nat := a.outputs.length + a.refusals.length

structure Measured where
  receipt : Receipt
  work : Nat
  copied : Nat
  prunedCalls : Nat
  deriving Repr

def meterAttempt (f : GTree → List Group → List Vertex → Measured)
    (t : GTree) (d : List Group) (c : List Vertex) (g : Group) : Measured :=
  if g.origin = [] then ⟨⟨[],["attempt to cut original root"],0,1,0⟩,0,0,0⟩
  else if c.contains g.origin then ⟨⟨[],["duplicate original source cut"],0,1,0⟩,0,0,0⟩
  else match erase g.origin t with
  | none => ⟨⟨[],["attempt removed entire current source"],0,1,0⟩,0,0,0⟩
  | some next =>
    let r := f next (g :: d) (g.origin :: c)
    { r with receipt := { r.receipt with childAttempts := r.receipt.childAttempts + 1 } }

def meterStep (f : GTree → List Group → List Vertex → Measured)
    (current : GTree) (d : List Group) (c : List Vertex) : Measured :=
  let t := normalize current
  let charge := localCharge current d c
  match choose t with
  | .finish =>
    ⟨⟨[⟨d.map Group.labels ++ [(groups t).flatMap Group.labels],c⟩],[],1,0,0⟩,charge,0,0⟩
  | .one g =>
    let r := meterAttempt f t d c g
    ⟨prefixRoot r.receipt, charge + r.work,r.copied,r.prunedCalls⟩
  | .two a b =>
    let ra := meterAttempt f t d c a
    let rb := meterAttempt f t d c b
    let copies := appendCells ra.receipt
    ⟨prefixRoot (combine ra.receipt rb.receipt), charge + ra.work + rb.work + copies,
      ra.copied + rb.copied + copies,ra.prunedCalls + rb.prunedCalls⟩
  | .refuse why => ⟨⟨[],[why],1,0,0⟩,charge,0,0⟩

def meterRun : Nat → GTree → List Group → List Vertex → Measured
  | 0 => meterStep (fun _ _ _ => ⟨⟨[],[],0,0,1⟩,1,0,1⟩)
  | q+1 => meterStep (meterRun q)

theorem meterAttempt_receipt (f : GTree → List Group → List Vertex → Measured) (t d c g) :
    (meterAttempt f t d c g).receipt = attempt (fun t d c => (f t d c).receipt) t d c g := by
  unfold meterAttempt attempt
  split <;> try rfl
  split <;> try rfl
  cases he : erase g.origin t <;> simp only [he]

theorem meterStep_receipt (f : GTree → List Group → List Vertex → Measured) (t d c) :
    (meterStep f t d c).receipt = step (fun t d c => (f t d c).receipt) t d c := by
  cases hs : choose (normalize t) <;>
    simp only [meterStep,step,hs,meterAttempt_receipt]

theorem meterRun_receipt (q : Nat) (t d c) :
    (meterRun q t d c).receipt = run q t d c := by
  induction q generalizing t d c with
  | zero => exact meterStep_receipt _ t d c
  | succ q ih =>
    simp only [meterRun,meterStep_receipt,run]
    congr 1
    funext t d c
    exact ih t d c

/-- Budget-pruned calls are exactly the frozen Receipt.pruned counter. -/
theorem meterAttempt_pruned (f : GTree → List Group → List Vertex → Measured)
    (hf : ∀ t d c, (f t d c).prunedCalls = (f t d c).receipt.pruned) (t d c g) :
    (meterAttempt f t d c g).prunedCalls = (meterAttempt f t d c g).receipt.pruned := by
  unfold meterAttempt
  split <;> try rfl
  split <;> try rfl
  split <;> first | rfl | exact hf _ _ _

theorem meterRun_pruned (q : Nat) (t d c) :
    (meterRun q t d c).prunedCalls = (run q t d c).pruned := by
  have aux (f : GTree → List Group → List Vertex → Measured)
      (hf : ∀ t d c, (f t d c).prunedCalls = (f t d c).receipt.pruned) (t d c) :
      (meterStep f t d c).prunedCalls = (meterStep f t d c).receipt.pruned := by
    cases hs : choose (normalize t) <;>
      simp only [meterStep,hs,prefixRoot,combine,meterAttempt_pruned f hf]
  rw [← meterRun_receipt]
  induction q generalizing t d c with
  | zero => exact aux _ (by intros; rfl) t d c
  | succ q ih => exact aux _ ih t d c

theorem attempt_records (f : GTree → List Group → List Vertex → Receipt)
    (hf : ∀ t d c, records (f t d c) ≤ (f t d c).visited + (f t d c).childAttempts)
    (t d c g) :
    records (attempt f t d c g) ≤ (attempt f t d c g).visited + (attempt f t d c g).childAttempts := by
  unfold attempt
  split
  · simp [records]
  · split
    · simp [records]
    · split
      · simp [records]
      · rename_i next he
        have hh := hf next (g::d) (g.origin::c)
        simp only [records] at *
        omega

theorem run_records_events (q : Nat) (t d c) :
    records (run q t d c) ≤ (run q t d c).visited + (run q t d c).childAttempts := by
  have aux (f : GTree → List Group → List Vertex → Receipt)
      (hf : ∀ t d c, records (f t d c) ≤ (f t d c).visited + (f t d c).childAttempts) (t d c) :
      records (step f t d c) ≤ (step f t d c).visited + (step f t d c).childAttempts := by
    cases hs : choose (normalize t) with
    | finish => simp [step,hs,records]
    | refuse s => simp [step,hs,records]
    | one g =>
      have hh := attempt_records f hf (normalize t) d c g
      simpa only [step,hs,prefixRoot,records] using Nat.le_trans hh (by omega)
    | two a b =>
      have ha := attempt_records f hf (normalize t) d c a
      have hb := attempt_records f hf (normalize t) d c b
      simp only [step,hs,prefixRoot,combine,records,List.length_append] at *
      omega
  induction q generalizing t d c with
  | zero => exact aux _ (by intros; simp [records]) t d c
  | succ q ih => exact aux _ ih t d c

theorem run_records_bound (q : Nat) (t d c) :
    records (run q t d c) ≤ 3 * 2^(q+1) := by
  have he := run_records_events q t d c
  have hb := run_prefix_work_bound q t d c
  omega

/-- Source-local resource condition; no runtime/simulation hypothesis. -/
def Within (m q : Nat) (t : GTree) (d : List Group) (c : List Vertex) : Prop :=
  footprint t + d.length + c.length + 2*q ≤ m

def cap (m : Nat) : Nat := 256*(m+1)^3

theorem local_le_cap (m q t d c) (h : Within m q t d c) : localCharge t d c ≤ cap m := by
  unfold Within at h
  have hh : footprint t + d.length + c.length + 1 ≤ m+1 := by omega
  exact Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left hh 3)

theorem continuation_within (m q t d c g next)
    (h : Within m (q+1) t d c) (he : erase g.origin (normalize t) = some next) :
    Within m q next (g::d) (g.origin::c) := by
  have hn := normalize_footprint t
  have hh := erase_footprint _ _ _ he
  unfold Within at *
  simp only [List.length_cons]
  omega

/-- Recurrence includes actual receipt materialization: the left result list can
have exponentially many records, so combine is never charged as a constant. -/
def envelope (q l : Nat) : Nat :=
  match q with
  | 0 => l+3
  | q+1 => l + 2*envelope q l + 3*2^(q+1)

theorem meterAttempt_work (f : GTree → List Group → List Vertex → Measured)
    (n : Nat) (hf : ∀ next, erase g.origin t = some next →
      (f next (g::d) (g.origin::c)).work ≤ n) :
    (meterAttempt f t d c g).work ≤ n := by
  unfold meterAttempt
  split <;> try exact Nat.zero_le _
  split <;> try exact Nat.zero_le _
  split
  · exact Nat.zero_le _
  · exact hf _ ‹_›

theorem meterAttempt_records (f : GTree → List Group → List Vertex → Measured)
    (n : Nat) (hn : 1 ≤ n)
    (hf : ∀ t d c, records (f t d c).receipt ≤ n) (t d c g) :
    records (meterAttempt f t d c g).receipt ≤ n := by
  unfold meterAttempt
  split
  · simpa [records] using hn
  · split
    · simpa [records] using hn
    · split
      · simpa [records] using hn
      · exact hf _ _ _

theorem meterRun_bound (q : Nat) (m t d c) (h : Within m q t d c) :
    (meterRun q t d c).work ≤ envelope q (cap m) := by
  induction q generalizing t d c with
  | zero =>
    have hl := local_le_cap m 0 t d c h
    cases hs : choose (normalize t) with
    | finish => simp only [meterRun,meterStep,hs,envelope]; omega
    | refuse why => simp only [meterRun,meterStep,hs,envelope]; omega
    | one g =>
      have hw := meterAttempt_work (t := normalize t) (d := d) (c := c) (g := g)
        (fun _ _ _ => (⟨⟨[],[],0,0,1⟩,1,0,1⟩ : Measured)) 1 (by intros; exact Nat.le_refl _)
      simp only [meterRun,meterStep,hs,envelope]
      omega
    | two a b =>
      let f := fun (_ : GTree) (_ : List Group) (_ : List Vertex) => (⟨⟨[],[],0,0,1⟩,1,0,1⟩ : Measured)
      have ha := meterAttempt_work (t := normalize t) (d := d) (c := c) (g := a) f 1 (by intros; exact Nat.le_refl _)
      have hb := meterAttempt_work (t := normalize t) (d := d) (c := c) (g := b) f 1 (by intros; exact Nat.le_refl _)
      have hr := meterAttempt_records f 1 (Nat.le_refl _) (by intros; simp [f,records]) (normalize t) d c a
      change appendCells _ ≤ 1 at hr
      simp only [meterRun,meterStep,hs,envelope]
      change localCharge t d c + (meterAttempt f (normalize t) d c a).work +
        (meterAttempt f (normalize t) d c b).work + appendCells (meterAttempt f (normalize t) d c a).receipt ≤ cap m + 3
      omega
  | succ q ih =>
    have hl := local_le_cap m (q+1) t d c h
    have hw (g : Group) : (meterAttempt (meterRun q) (normalize t) d c g).work ≤ envelope q (cap m) := by
      apply meterAttempt_work
      intro next he
      exact ih next (g::d) (g.origin::c) (continuation_within m q t d c g next h he)
    have hp : 1 ≤ 3*2^(q+1) := by
      have hh : 1 ≤ 2^(q+1) := Nat.one_le_pow _ _ (by decide)
      omega
    have hr (g : Group) : appendCells (meterAttempt (meterRun q) (normalize t) d c g).receipt ≤ 3*2^(q+1) := by
      apply meterAttempt_records (meterRun q) _ hp
      intro t d c
      rw [meterRun_receipt]
      exact run_records_bound q t d c
    cases hs : choose (normalize t) with
    | finish => simp only [meterRun,meterStep,hs,envelope]; omega
    | refuse why => simp only [meterRun,meterStep,hs,envelope]; omega
    | one g =>
      have hh := hw g
      simp only [meterRun,meterStep,hs,envelope]
      omega
    | two a b =>
      have ha := hw a
      have hb := hw b
      have hh := hr a
      simp only [meterRun,meterStep,hs,envelope]
      omega


theorem envelope_closed (q l : Nat) :
    envelope q l ≤ (l+6)*(q+1)*2^(q+1) := by
  induction q with
  | zero => simp only [envelope]; omega
  | succ q ih =>
    let p := 2^(q+1)
    change envelope q l ≤ (l+6)*(q+1)*p at ih
    have hp : 1 ≤ p := Nat.one_le_pow _ _ (by decide)
    have hl : l ≤ l*p := by simpa using Nat.mul_le_mul_left l hp
    have htail : l + 3*p ≤ 2*((l+6)*p) := by
      simp only [Nat.add_mul] at *
      omega
    have hexpand : (l+6)*(q+1+1)*2^(q+1+1) =
        2*((l+6)*(q+1)*p) + 2*((l+6)*p) := by
      simp only [p,Nat.pow_succ,Nat.mul_add,Nat.add_mul,Nat.mul_one]
      ac_rfl
    rw [hexpand]
    change l + 2*envelope q l + 3*p ≤ _
    omega

/-- One concrete syntactic oracle invocation per leaf. These calls are not
assumed computable in polynomial time. Returned values are literal fromTree. -/
structure Initial where
  tree : GTree
  oracleCalls : Nat
  deriving Repr

def meterFromTree (color : Nat → Nat) (p : Vertex) : Tree → Initial
  | .leaf x => ⟨.leaf ⟨p,[x],color x⟩,1⟩
  | .node l r =>
    let a := meterFromTree color (p++[false]) l
    let b := meterFromTree color (p++[true]) r
    ⟨.node p a.tree b.tree,a.oracleCalls+b.oracleCalls⟩

theorem meterFromTree_tree (color p t) :
    (meterFromTree color p t).tree = fromTree color p t := by
  induction t generalizing p with
  | leaf x => rfl
  | node l r ihl ihr => simp only [meterFromTree,fromTree,ihl,ihr]

theorem meterFromTree_calls (color p t) :
    (meterFromTree color p t).oracleCalls = (leaves t).length := by
  induction t generalizing p with
  | leaf x => rfl
  | node l r ihl ihr => simp only [meterFromTree,leaves,List.length_append,ihl,ihr]

/-- Covers the complete leaves/Nodup/fromTree preparation and min/subtract in
source operations. Scalar bit costs, including arbitrary input budget, are
converted separately. Oracle evaluation itself is excluded and exposed. -/
def initialCharge (t : Tree) : Nat := 128*(treeNodes t+1)^3

/-- Polynomial in actual source constructor count; independent of colors. -/
def inputResource (t : Tree) : Nat :=
  treeNodes t*(treeNodes t+2) + treeNodes t+1

structure Generated where
  measured : Measured
  oracleCalls : Nat
  deriving Repr

def meterGenerate (t : Tree) (color : Nat → Nat) (budget : Nat) : Generated :=
  if (leaves t).Nodup then
    let init := meterFromTree color [] t
    let r := meterRun (min budget ((leaves t).length-1)) init.tree [] []
    ⟨{r with work := initialCharge t+r.work},init.oracleCalls⟩
  else ⟨⟨⟨[],["duplicate original label"],0,0,0⟩,initialCharge t,0,0⟩,0⟩

theorem meterGenerate_receipt (t color budget) :
    (meterGenerate t color budget).measured.receipt = generate t color budget := by
  unfold meterGenerate generate
  split
  · simp only [meterFromTree_tree,meterRun_receipt]
  · rfl

theorem meterGenerate_calls (t color budget) :
    (meterGenerate t color budget).oracleCalls =
      if (leaves t).Nodup then (leaves t).length else 0 := by
  unfold meterGenerate
  split <;> simp only [meterFromTree_calls]

theorem initial_within (t : Tree) (color : Nat → Nat) (budget : Nat) :
    Within (inputResource t) (min budget ((leaves t).length-1))
      (fromTree color [] t) [] [] := by
  have hf := fromTree_footprint color [] t
  have hb := Nat.min_le_right budget ((leaves t).length-1)
  have hn := treeNodes_le_twice_leaves t
  simp only [List.length_nil,Nat.zero_add] at hf
  unfold Within inputResource
  simp only [List.length_nil,Nat.add_zero]
  omega

theorem generate_work_bound (t : Tree) (color : Nat → Nat) (budget : Nat) :
    (meterGenerate t color budget).measured.work ≤ initialCharge t +
      (cap (inputResource t)+6)*(min budget ((leaves t).length-1)+1)*
        2^(min budget ((leaves t).length-1)+1) := by
  unfold meterGenerate
  split
  · simp only [meterFromTree_tree]
    have hw := meterRun_bound _ (inputResource t) _ [] [] (initial_within t color budget)
    have he := envelope_closed (min budget ((leaves t).length-1)) (cap (inputResource t))
    omega
  · exact Nat.le_add_right _ _

end Universal233.CoreWork
