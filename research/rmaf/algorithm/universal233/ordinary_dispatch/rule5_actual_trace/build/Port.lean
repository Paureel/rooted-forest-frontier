import MarkerBounds
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge Universal233.CoreGraph

/-- A single actual original subtree hole. Other branches retain their full
original trees; clipping suppresses a branch only when its restriction is empty. -/
inductive Port where
  | hole
  | left (c : Port) (r : Tree)
  | right (l : Tree) (c : Port)
deriving DecidableEq, Repr

def Port.plug : Port → Tree → Tree
  | .hole,u => u
  | .left c r,u => .node (c.plug u) r
  | .right l c,u => .node l (c.plug u)

def Port.labels : Port → List Nat
  | .hole => []
  | .left c r => c.labels++leaves r
  | .right l c => leaves l++c.labels

def Port.clip (U : List Nat) : Port → Port
  | .hole => .hole
  | .left c r => match restrict U r with
    | none => c.clip U
    | some v => .left (c.clip U) v
  | .right l c => match restrict U l with
    | none => c.clip U
    | some v => .right v (c.clip U)

theorem Port.restrict_plug (c : Port) (u v : Tree) (U : List Nat)
    (hu : restrict U u=some v) :
    restrict U (c.plug u)=some ((c.clip U).plug v) := by
  induction c with
  | hole => exact hu
  | left c r ih =>
    cases hr : restrict U r <;> simp only [Port.plug,restrict,ih,Port.clip,hr]
  | right l c ih =>
    cases hl : restrict U l <;> simp only [Port.plug,restrict,ih,Port.clip,hl]

theorem Port.clip_congr (c : Port) (U V : List Nat)
    (h : ∀ x∈c.labels, x∈U ↔ x∈V) : c.clip U=c.clip V := by
  induction c with
  | hole => rfl
  | left c r ih =>
    have hr : restrict U r=restrict V r := BinaryExchange.restrict_congr r U V
      (by intro x hx;exact h x (List.mem_append_right _ hx))
    have hc := ih (by intro x hx;exact h x (List.mem_append_left _ hx))
    simp only [Port.clip,hr,hc]
  | right l c ih =>
    have hl : restrict U l=restrict V l := BinaryExchange.restrict_congr l U V
      (by intro x hx;exact h x (List.mem_append_left _ hx))
    have hc := ih (by intro x hx;exact h x (List.mem_append_right _ hx))
    simp only [Port.clip,hl,hc]

theorem Port.leaves_perm (c : Port) (u : Tree) :
    (leaves (c.plug u)).Perm (c.labels++leaves u) := by
  induction c with
  | hole => simp [Port.plug,Port.labels]
  | left c r ih =>
    simp only [Port.plug,Port.labels,leaves]
    apply (ih.append_right (leaves r)).trans
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁:=leaves u) (l₂:=leaves r)).append_left c.labels
  | right l c ih =>
    simpa only [Port.plug,Port.labels,leaves,List.append_assoc] using ih.append_left (leaves l)

/-- Every literal original address, including the root boundary, gives an
actual one-hole decomposition. No displayed/suppressed edge is substituted. -/
theorem original_port (T u : Tree) (p : RMAF.Vertex) (h : subtree T p=some u) :
    ∃ c : Port, T=c.plug u := by
  induction p generalizing T with
  | nil => exact ⟨.hole,Option.some.inj h⟩
  | cons b p ih =>
    cases T with
    | leaf x => simp [subtree] at h
    | node l r =>
      cases b with
      | false =>
        obtain ⟨c,hc⟩ := ih l h
        exact ⟨.left c r,by rw [Port.plug,←hc]⟩
      | true =>
        obtain ⟨c,hc⟩ := ih r h
        exact ⟨.right l c,by rw [Port.plug,←hc]⟩

def graft (y : Nat) (u : Tree) : Tree → Tree
  | .leaf x => if x=y then u else .leaf x
  | .node a b => .node (graft y u a) (graft y u b)

theorem graft_iso (y : Nat) (u v t s : Tree) (hu : RootedIso u v) (ht : RootedIso t s) :
    RootedIso (graft y u t) (graft y v s) := by
  induction ht with
  | leaf x => by_cases h : x=y <;> simp only [graft,h,ite_true,ite_false]
              · exact hu
              · exact .leaf _
  | straight h1 h2 ih1 ih2 => exact .straight ih1 ih2
  | swapped h1 h2 ih1 ih2 => exact .swapped ih1 ih2

theorem graft_absent (y : Nat) (u t : Tree) (h : y∉leaves t) : graft y u t=t := by
  induction t with
  | leaf x => have hn : x≠y := by simpa [leaves,eq_comm] using h
              simp [graft,hn]
  | node a b ha hb =>
    have hn : y∉leaves a ∧ y∉leaves b := by simpa [leaves] using h
    simp only [graft,ha hn.1,hb hn.2]

theorem Port.graft_hole (c : Port) (y : Nat) (u : Tree) (h : y∉c.labels) :
    graft y u (c.plug (.leaf y))=c.plug u := by
  induction c with
  | hole => simp [Port.plug,graft]
  | left c r ih =>
    have hn : y∉c.labels ∧ y∉leaves r := by simpa [Port.labels] using h
    simp only [Port.plug,graft,ih hn.1,graft_absent y u r hn.2]
  | right l c ih =>
    have hn : y∉leaves l ∧ y∉c.labels := by simpa [Port.labels] using h
    simp only [Port.plug,graft,ih hn.2,graft_absent y u l hn.1]

/-- Genuine topology gluing for the same oriented source cut: matching ported
restrictions and matching inserted subtrees give matching original unions. -/
theorem port_glue_same_orientation (c d : Port) (u v : Tree) (y : Nat)
    (hc : y∉c.labels) (hd : y∉d.labels)
    (hp : RootedIso (c.plug (.leaf y)) (d.plug (.leaf y))) (hi : RootedIso u v) :
    RootedIso (c.plug u) (d.plug v) := by
  have hh := graft_iso y u v _ _ hi hp
  simpa only [Port.graft_hole c y u hc,Port.graft_hole d y v hd] using hh
end OrdinaryCommonSplit
