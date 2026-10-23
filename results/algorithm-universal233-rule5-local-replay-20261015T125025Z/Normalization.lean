import Contraction

/-! One-shot graph semantics for the exact CoreProgram.normalize operation.
The skeleton is the actual binary graph, with group colors as leaf labels;
original taxon payloads are carried by Group and the proved transport map. -/
namespace Universal233.Integration
open RMAF CoreGraph CoreProgram

def skeleton : GTree → Tree
  | .leaf g => .leaf g.color
  | .node _ l r => .node (skeleton l) (skeleton r)

def groupAt : GTree → RMAF.Vertex → Option Group
  | .leaf g, [] => some g
  | .leaf _, _ :: _ => none
  | .node _ _ _, [] => none
  | .node _ l r, s :: v => groupAt (if s then r else l) v

def GroupLeafAt (t : GTree) (v : RMAF.Vertex) (g : Group) : Prop := groupAt t v = some g

theorem groupLeaf_leaf (a g : Group) (v : RMAF.Vertex) :
    GroupLeafAt (.leaf a) v g ↔ v = [] ∧ a = g := by
  cases v <;> simp [GroupLeafAt,groupAt]

theorem groupLeaf_skeleton (t : GTree) (v : RMAF.Vertex) (g : Group)
    (h : GroupLeafAt t v g) : LeafAt (skeleton t) v g.color := by
  induction t generalizing v with
  | leaf a =>
    obtain ⟨rfl,rfl⟩ := (groupLeaf_leaf a g v).1 h
    rfl
  | node origin l r ihl ihr =>
    cases v with
    | nil => simp [GroupLeafAt,groupAt] at h
    | cons s v => cases s <;> first | exact ihl v h | exact ihr v h

inductive GContract : GTree → GTree → RMAF.Vertex → Nat → Prop
  | root (origin : RMAF.Vertex) (a b : Group) (hc : a.color = b.color) :
      GContract (.node origin (.leaf a) (.leaf b))
        (.leaf ⟨origin,a.labels ++ b.labels,a.color⟩) [] a.color
  | left {t u p c} (origin : RMAF.Vertex) (r : GTree) : GContract t u p c →
      GContract (.node origin t r) (.node origin u r) (false :: p) c
  | right {t u p c} (origin : RMAF.Vertex) (l : GTree) : GContract t u p c →
      GContract (.node origin l t) (.node origin l u) (true :: p) c

theorem gcontract_graph {t u p c} (h : GContract t u p c) :
    CherryContraction (skeleton t) (skeleton u) p c c c := by
  induction h with
  | root origin a b hc => simpa [skeleton,hc] using CherryContraction.root b.color b.color b.color
  | left origin r h ih => exact .left (skeleton r) ih
  | right origin l h ih => exact .right (skeleton l) ih

theorem projection_cons (s : Bool) (p v : RMAF.Vertex) :
    cherryProjection (s :: p) (s :: v) = s :: cherryProjection p v := by
  simp only [cherryProjection,List.cons_append,List.cons.injEq,true_and]
  split <;> rfl

theorem projection_other (s : Bool) (p v : RMAF.Vertex) :
    cherryProjection (s :: p) ((!s) :: v) = (!s) :: v := by
  cases s <;> simp [cherryProjection]

/-- Every original group occurrence has a concrete quotient leaf whose payload
contains its entire original-label set. No original labels are recolored. -/
theorem gcontract_group_image {t u p c} (h : GContract t u p c)
    (v : RMAF.Vertex) (g : Group) (hv : GroupLeafAt t v g) :
    ∃ a, GroupLeafAt u (cherryProjection p v) a ∧ ∀ x, x ∈ g.labels → x ∈ a.labels := by
  induction h generalizing v with
  | root origin a b hc =>
    cases v with
    | nil => simp [GroupLeafAt,groupAt] at hv
    | cons s v =>
      cases s with
      | false =>
        obtain ⟨rfl,rfl⟩ := (groupLeaf_leaf a g v).1 hv
        exact ⟨⟨origin,a.labels ++ b.labels,a.color⟩,rfl,fun x hx => List.mem_append_left _ hx⟩
      | true =>
        obtain ⟨rfl,rfl⟩ := (groupLeaf_leaf b g v).1 hv
        exact ⟨⟨origin,a.labels ++ b.labels,a.color⟩,rfl,fun x hx => List.mem_append_right _ hx⟩
  | left origin r h ih =>
    cases v with
    | nil => simp [GroupLeafAt,groupAt] at hv
    | cons s v =>
      cases s with
      | false =>
        obtain ⟨a,ha,hlab⟩ := ih v hv
        exact ⟨a,by simpa [projection_cons,GroupLeafAt,groupAt] using ha,hlab⟩
      | true => exact ⟨g,by simpa [cherryProjection,GroupLeafAt,groupAt] using hv,fun x hx => hx⟩
  | right origin l h ih =>
    cases v with
    | nil => simp [GroupLeafAt,groupAt] at hv
    | cons s v =>
      cases s with
      | false => exact ⟨g,by simpa [cherryProjection,GroupLeafAt,groupAt] using hv,fun x hx => hx⟩
      | true =>
        obtain ⟨a,ha,hlab⟩ := ih v hv
        exact ⟨a,by simpa [projection_cons,GroupLeafAt,groupAt] using ha,hlab⟩

/-- Original group lift plus source-partition coarsening along an actual graph
quotient. The witness map composes through arbitrarily many contractions. -/
def GroupedTransport (t u : GTree) (P : SourcePartition (skeleton t))
    (Q : SourcePartition (skeleton u)) : Prop :=
  ∃ f : RMAF.Vertex → RMAF.Vertex,
    (∀ v g, GroupLeafAt t v g → ∃ a, GroupLeafAt u (f v) a ∧
      ∀ x, x ∈ g.labels → x ∈ a.labels) ∧
    (∀ v w g a, GroupLeafAt t v g → GroupLeafAt t w a →
      P.owner v = P.owner w → Q.owner (f v) = Q.owner (f w))

theorem groupedTransport_refl (t : GTree) (P : SourcePartition (skeleton t)) :
    GroupedTransport t t P P :=
  ⟨id,(by intro v g hv; exact ⟨g,hv,fun x hx => hx⟩),(by intros; assumption)⟩

theorem groupedTransport_trans {t u v : GTree}
    {P : SourcePartition (skeleton t)} {Q : SourcePartition (skeleton u)}
    {R : SourcePartition (skeleton v)}
    (h : GroupedTransport t u P Q) (k : GroupedTransport u v Q R) :
    GroupedTransport t v P R := by
  obtain ⟨f,hf,hr⟩ := h
  obtain ⟨g,hg,hs⟩ := k
  refine ⟨g ∘ f,?_,?_⟩
  · intro w a ha
    obtain ⟨b,hb,hlab⟩ := hf w a ha
    obtain ⟨c,hc,hlbc⟩ := hg (f w) b hb
    exact ⟨c,hc,fun x hx => hlbc x (hlab x hx)⟩
  · intro a b ga gb ha hb he
    obtain ⟨ga',ha',_⟩ := hf a ga ha
    obtain ⟨gb',hb',_⟩ := hf b gb hb
    exact hs _ _ _ _ ha' hb' (hr _ _ _ _ ha hb he)

/-- One executable homogeneous group rewrite has an actual source graph
coarsening and quotient, with an original-label lift. -/
theorem gcontract_transport {t u p c} (h : GContract t u p c)
    (P : SourcePartition (skeleton t)) (hm : Monochromatic P id) :
    ∃ Q : SourcePartition (skeleton u), Monochromatic Q id ∧ GroupedTransport t u P Q := by
  have hc := gcontract_graph h
  have hch := contraction_cherry hc
  obtain ⟨P',hPP',hm',hs⟩ := homogeneous_cherry_coarsening P hch id hm rfl
  let Q := contractPartition hc P' hs
  refine ⟨Q,contractPartition_monochromatic hc P' hs id hm' rfl,?_⟩
  refine ⟨cherryProjection p,gcontract_group_image h,?_⟩
  intro v w g a hv hw he
  have hlv := groupLeaf_skeleton t v g hv
  have hlw := groupLeaf_skeleton t w a hw
  have ho := hPP' _ _ _ _ hlv hlw he
  change (contractPartition hc P' hs).owner _ = (contractPartition hc P' hs).owner _
  rw [contractPartition_owner hc P' hs v g.color hlv,contractPartition_owner hc P' hs w a.color hlw]
  exact ho

inductive GContracts : GTree → GTree → Prop
  | refl (t : GTree) : GContracts t t
  | step {t u v p c} : GContract t u p c → GContracts u v → GContracts t v

theorem gcontracts_trans {t u v} (h : GContracts t u) (k : GContracts u v) : GContracts t v := by
  induction h with
  | refl => exact k
  | step hr hs ih => exact .step hr (ih k)

theorem gcontracts_left {t u} (h : GContracts t u) (origin : RMAF.Vertex) (r : GTree) :
    GContracts (.node origin t r) (.node origin u r) := by
  induction h with
  | refl => exact .refl _
  | step hr hs ih => exact .step (.left origin r hr) ih

theorem gcontracts_right {t u} (h : GContracts t u) (origin : RMAF.Vertex) (l : GTree) :
    GContracts (.node origin l t) (.node origin l u) := by
  induction h with
  | refl => exact .refl _
  | step hr hs ih => exact .step (.right origin l hr) ih

/-- The exact recursive CoreProgram.normalize is a finite composition of the
actual homogeneous cherry graph rewrites proved above. -/
theorem normalize_gcontracts (t : GTree) : GContracts t (normalize t) := by
  induction t with
  | leaf g => exact .refl _
  | node origin l r ihl ihr =>
    have hs := gcontracts_trans (gcontracts_left ihl origin r)
      (gcontracts_right ihr origin (normalize l))
    apply gcontracts_trans hs
    cases hl : normalize l with
    | leaf a =>
      cases hr : normalize r with
      | leaf b =>
        simp only [normalize,hl,hr]
        split
        next hc => exact .step (.root origin a b hc) (.refl _)
        next hc => exact .refl _
      | node p a b => simp only [normalize,hl,hr]; exact .refl _
    | node p a b =>
      cases hr : normalize r <;> simp only [normalize,hl,hr] <;> exact .refl _

theorem gcontracts_transport {t u} (h : GContracts t u)
    (P : SourcePartition (skeleton t)) (hm : Monochromatic P id) :
    ∃ Q : SourcePartition (skeleton u), Monochromatic Q id ∧ GroupedTransport t u P Q := by
  induction h with
  | refl => exact ⟨P,hm,groupedTransport_refl _ _⟩
  | step hr hs ih =>
    obtain ⟨Q,hQ,hPQ⟩ := gcontract_transport hr P hm
    obtain ⟨R,hR,hQR⟩ := ih Q hQ
    exact ⟨R,hR,groupedTransport_trans hPQ hQR⟩

/-- The exact first internal normalization call has source graph simulation,
monochromatic coarsening and a compositional original-label group lift.
This theorem needs neither reachable-state assumptions nor an abstract graph
quotient axiom. Erase/suppression and original cut realization are separate. -/
theorem normalize_source_transport (t : GTree) (P : SourcePartition (skeleton t))
    (hm : Monochromatic P id) :
    ∃ Q : SourcePartition (skeleton (normalize t)), Monochromatic Q id ∧
      GroupedTransport t (normalize t) P Q :=
  gcontracts_transport (normalize_gcontracts t) P hm

end Universal233.Integration
