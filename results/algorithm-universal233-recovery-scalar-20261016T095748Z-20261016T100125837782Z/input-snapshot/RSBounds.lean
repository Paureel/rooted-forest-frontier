import RSBinaryCopy
namespace OrdinaryDispatch.RecoveryScalar
open RMAF Universal233 CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits

def GroupValues (B : Nat) (g : Group) : Prop :=
 (∀ x∈g.labels, x<B) ∧ g.color<B

def TreeValues (B : Nat) : GTree→Prop
 | .leaf g=>GroupValues B g
 | .node _ l r=>TreeValues B l ∧ TreeValues B r

theorem fromTree_values (B : Nat) (color : Nat→Nat) (p : Vertex) (t : Tree)
 (labels : ∀ x∈leaves t,x<B) (colors : ∀ x∈leaves t,color x<B) :
 TreeValues B (fromTree color p t) := by
 induction t generalizing p with
 | leaf x=>simpa [fromTree,TreeValues,GroupValues,leaves] using And.intro (labels x (by simp [leaves])) (colors x (by simp [leaves]))
 | node l r il ir=>
  exact ⟨il _ (by intro x hx;exact labels x (by simp [leaves,hx])) (by intro x hx;exact colors x (by simp [leaves,hx])),
   ir _ (by intro x hx;exact labels x (by simp [leaves,hx])) (by intro x hx;exact colors x (by simp [leaves,hx]))⟩

theorem normalize_values (B : Nat) (t : GTree) (h : TreeValues B t) : TreeValues B (normalize t) := by
 induction t with
 | leaf g=>exact h
 | node p l r il ir=>
  have a:=il h.1;have b:=ir h.2
  cases hl:normalize l with
  | leaf x=>
   cases hr:normalize r with
   | leaf y=>
    simp only [hl,hr,TreeValues] at a b
    simp only [normalize,hl,hr]
    split
    · exact ⟨by intro z hz;rcases List.mem_append.mp hz with hz|hz;exact a.1 z hz;exact b.1 z hz,a.2⟩
    · exact ⟨a,b⟩
   | node q x y=>simpa [normalize,hl,hr,TreeValues] using And.intro a b
  | node q x y=>cases hr:normalize r <;> simpa [normalize,hl,hr,TreeValues] using And.intro a b

theorem erase_values (B : Nat) (v : Vertex) (t u : GTree) (h : TreeValues B t)
 (e : erase v t=some u) : TreeValues B u := by
 induction t generalizing u with
 | leaf g=>simp only [erase] at e;split at e;contradiction;cases e;exact h
 | node p l r il ir=>
  simp only [erase] at e
  split at e
  · contradiction
  · cases hl:erase v l <;> cases hr:erase v r <;> simp only [hl,hr] at e
    · contradiction
    · cases e;exact ir _ h.2 hr
    · cases e;exact il _ h.1 hl
    · cases e;exact ⟨il _ h.1 hl,ir _ h.2 hr⟩

theorem group_values (B : Nat) (t : GTree) (h : TreeValues B t) (g : Group) (mem : g∈groups t) : GroupValues B g := by
 induction t with
 | leaf a=>
  have eq:g=a:=by simpa [groups] using mem
  subst g
  exact h
 | node p l r il ir=>
  rcases List.mem_append.mp mem with mem|mem
  · exact il h.1 mem
  · exact ir h.2 mem

theorem chosen_one_mem (t : GTree) (g : Group) (h : choose t=.one g) : g∈groups t :=
 (Integration.choose_one_selected t g h).1

theorem chosen_two_mem (t : GTree) (a b : Group) (h : choose t=.two a b) : a∈groups t ∧ b∈groups t := by
 obtain ⟨p,cherry,_⟩:=Integration.choose_two_selected t a b h
 exact ⟨Integration.groupLeaf_mem_groups t (p++[false]) a (Integration.gcherry_left cherry),
  Integration.groupLeaf_mem_groups t (p++[true]) b (Integration.gcherry_right cherry)⟩

structure StateCap (N B q : Nat) (t : GTree) (d : List Group) (c : List Vertex) : Prop where
 within : Within N q t d c
 tree : TreeValues B t
 detached : ∀ g∈d, GroupValues B g ∧ g.labels.length≤N ∧ g.origin.length≤N
 cuts : ∀ v∈c,v.length≤N

theorem initial_caps (t : Tree) (color : Nat→Nat) (budget B : Nat)
 (labels : ∀ x∈leaves t,x<B) (colors : ∀ x∈leaves t,color x<B) :
 StateCap (inputResource t) B (min budget ((leaves t).length-1)) (fromTree color [] t) [] [] :=
 ⟨initial_within t color budget,fromTree_values B color [] t labels colors,by simp,by simp⟩

theorem selected_caps (N B q : Nat) (t : GTree) (d : List Group) (c : List Vertex)
 (h : StateCap N B q t d c) (g : Group) (mem : g∈groups (normalize t)) :
 GroupValues B g ∧ g.labels.length≤N ∧ g.origin.length≤N := by
 have a:=group_values B (normalize t) (normalize_values B t h.tree) g mem
 have b:=group_size (normalize t) g mem
 have n:=normalize_footprint t
 have w:=h.within;dsimp only [Within] at w
 exact ⟨a,by omega,by omega⟩

theorem continuation_caps (N B q : Nat) (t : GTree) (d : List Group) (c : List Vertex)
 (h : StateCap N B (q+1) t d c) (g : Group) (mem : g∈groups (normalize t)) (next : GTree)
 (e : erase g.origin (normalize t)=some next) : StateCap N B q next (g::d) (g.origin::c) := by
 have sel:=selected_caps N B (q+1) t d c h g mem
 refine ⟨continuation_within N q t d c g next h.within e,erase_values B _ _ _ (normalize_values B t h.tree) e,?_,?_⟩
 · intro a ha;rcases List.mem_cons.mp ha with eq|ha
   · simpa [eq] using sel
   · exact h.detached a ha
 · intro v hv;rcases List.mem_cons.mp hv with eq|hv
   · simpa [eq] using sel.2.2
   · exact h.cuts v hv

/-- Overapproximates actual recursive callbacks: omitting guards admits extra
states, so root/duplicate refusals cannot invalidate a derived cap. -/
inductive Descendant (t : Tree) (color : Nat→Nat) (budget : Nat) : Nat→GTree→List Group→List Vertex→Prop where
 | root : Descendant t color budget (min budget ((leaves t).length-1)) (fromTree color [] t) [] []
 | child {q current d c g next} : Descendant t color budget (q+1) current d c→
   g∈groups (normalize current)→erase g.origin (normalize current)=some next→
   Descendant t color budget q next (g::d) (g.origin::c)

theorem descendant_caps (t : Tree) (color : Nat→Nat) (budget B : Nat)
 (labels : ∀ x∈leaves t,x<B) (colors : ∀ x∈leaves t,color x<B)
 {q current d c} (reach : Descendant t color budget q current d c) :
 StateCap (inputResource t) B q current d c := by
 induction reach with
 | root=>exact initial_caps t color budget B labels colors
 | child _ mem e ih=>exact continuation_caps _ _ _ _ _ _ ih _ mem _ e

theorem descendant_budget (t : Tree) (color : Nat→Nat) (budget : Nat)
 {q current d c} (reach : Descendant t color budget q current d c) :
 q≤min budget ((leaves t).length-1) := by
 induction reach with
 | root=>exact Nat.le_refl _
 | child _ _ _ ih=>omega

def eventSize (r : Receipt) : Nat := records r+r.visited+r.childAttempts+r.pruned

theorem attempt_events (f : GTree→List Group→List Vertex→Receipt) (B : Nat)
 (positive : 1≤B) (h : ∀ t d c,eventSize (f t d c)≤B) (t d c g) :
 eventSize (attempt f t d c g)≤B+1 := by
 unfold attempt
 split
 · simp [eventSize,records];omega
 · split
   · simp [eventSize,records];omega
   · split
     · simp [eventSize,records];omega
     · rename_i next e
       have a:=h next (g::d) (g.origin::c)
       simp only [eventSize,records] at a ⊢
       omega

theorem step_events (f : GTree→List Group→List Vertex→Receipt) (B : Nat)
 (positive : 1≤B) (h : ∀ t d c,eventSize (f t d c)≤B) (t d c) :
 eventSize (step f t d c)≤2*B+3 := by
 cases hc:choose (normalize t) with
 | finish=>simp [step,hc,eventSize,records]
 | refuse why=>simp [step,hc,eventSize,records]
 | one g=>have a:=attempt_events f B positive h (normalize t) d c g
          simp only [step,hc,prefixRoot,eventSize,records] at a ⊢;omega
 | two a b=>
  have x:=attempt_events f B positive h (normalize t) d c a
  have y:=attempt_events f B positive h (normalize t) d c b
  simp only [step,hc,prefixRoot,combine,eventSize,records,List.length_append] at x y ⊢;omega

theorem run_events (q : Nat) (t d c) : eventSize (run q t d c)+3≤8*2^(q+1) := by
 induction q generalizing t d c with
 | zero=>
  have a:=step_events (fun _ _ _=>⟨[],[],0,0,1⟩) 1 (by decide) (by intros;simp [eventSize,records]) t d c
  change eventSize (step (fun _ _ _=>⟨[],[],0,0,1⟩) t d c)+3≤8*2^1
  omega
 | succ q ih=>
  have positive:1≤8*2^(q+1)-3:=by have p:1≤2^(q+1):=Nat.one_le_pow _ _ (by decide);omega
  have a:=step_events (run q) (8*2^(q+1)-3) positive (by intro t d c;have h:=ih t d c;omega) t d c
  change eventSize (step (run q) t d c)+3≤8*2^(q+1+1)
  rw [Nat.pow_succ];omega

/-- Width for exponential receipt counters depends linearly on the clipped fuel,
not on the exponential number of retained records. -/
theorem run_counter_width (q Q : Nat) (hq : q≤Q) (t d c) :
 eventSize (run q t d c)<2^(Q+5) := by
 have a:=run_events q t d c
 have p:=Nat.pow_le_pow_right (n:=2) (by decide : 0<2) (Nat.add_le_add_right hq 1)
 have eq:8*2^(Q+1)=2^(Q+4):=by
  calc 8*2^(Q+1)=2^3*2^(Q+1):=rfl
       _=2^(3+(Q+1)):=(Nat.pow_add 2 3 (Q+1)).symm
       _=2^(Q+4):=by congr 1;omega
 have b:=Nat.mul_le_mul_left 8 p
 rw [eq] at b
 have grow:2^(Q+5)=2^(Q+4)*2:=by rw [show Q+5=(Q+4)+1 by omega,Nat.pow_succ]
 rw [grow]
 have pos:0<2^(Q+4):=Nat.pow_pos (by decide)
 omega

/-- This is a mathematical width certificate, never a runtime conversion. -/
def scalarWidth (N L Q : Nat) : Nat := L+2*labelBits (N+1)+Q+8

theorem scalar_width_inputs (N L Q : Nat) :
 N<2^(scalarWidth N L Q) ∧ 2^L≤2^(scalarWidth N L Q) ∧ 2^(Q+5)≤2^(scalarWidth N L Q) := by
 have a:labelBits N≤scalarWidth N L Q:=by
  have mono:=labelBits_mono N (N+1) (by omega)
  unfold scalarWidth;omega
 have b:L≤scalarWidth N L Q:=by unfold scalarWidth;omega
 have c:Q+5≤scalarWidth N L Q:=by unfold scalarWidth;omega
 exact ⟨Nat.lt_of_lt_of_le (Nat.lt_log2_self (n:=N)) (Nat.pow_le_pow_right (by decide) a),
  Nat.pow_le_pow_right (by decide) b,Nat.pow_le_pow_right (by decide) c⟩
end OrdinaryDispatch.RecoveryScalar
