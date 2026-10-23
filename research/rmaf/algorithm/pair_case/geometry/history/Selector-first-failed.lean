import Bridge
namespace PairGeometry
open VertexGeometry

theorem prefix_nil (a : Vertex) : Prefix [] a := ⟨a,rfl⟩

theorem prefix_cons (s t : Bool) (p a : Vertex) :
    Prefix (s::p) (t::a) ↔ s=t ∧ Prefix p a := by
  constructor
  · rintro ⟨q,hq⟩
    have hh : t=s ∧ a=p++q := List.cons.inj hq
    exact ⟨hh.1.symm,⟨q,hh.2⟩⟩
  · rintro ⟨rfl,q,rfl⟩; exact ⟨q,rfl⟩

theorem region_up_iff (v a : Vertex) : region v a = 2 ↔ ¬Prefix v a := by
  induction v generalizing a with
  | nil => simp [region_root_not_up, prefix_nil]
  | cons s v ih =>
    cases a with
    | nil => simp [region,Prefix]
    | cons t a =>
      by_cases h : s=t
      · subst t; simpa [region,prefix_cons] using ih a
      · simp [region,h,prefix_cons]

def side (s : Bool) : Nat := if s then 1 else 0

theorem region_child_iff (p a : Vertex) (s : Bool) :
    region p a = side s ↔ Prefix (p++[s]) a := by
  induction p generalizing a with
  | nil =>
    cases a with
    | nil => cases s <;> simp [region,side,Prefix]
    | cons t a => cases s <;> cases t <;> simp [region,side,prefix_cons,prefix_nil]
  | cons t p ih =>
    cases a with
    | nil => cases s <;> simp [region,side,Prefix]
    | cons u a =>
      by_cases h : t=u
      · subst u; simpa [region,prefix_cons] using ih a
      · cases s <;> simp [region,h,side,prefix_cons]

theorem edge_cross_path (p : Vertex) (s : Bool) (a b : Vertex)
    (ha : Prefix (p++[s]) a) (hb : ¬Prefix (p++[s]) b) :
    PathAt p a b ∧ PathAt (p++[s]) a b := by
  have hpa := (region_child_iff p a s).2 ha
  have hpb : region p b ≠ side s := by simpa [region_child_iff] using hb
  have hvb := (region_up_iff (p++[s]) b).2 hb
  have hva : region (p++[s]) a ≠ 2 := by
    intro h; exact (region_up_iff _ _).1 h ha
  exact ⟨region_ne_path _ _ _ (by simpa [hpa] using Ne.symm hpb),
    region_ne_path _ _ _ (by simpa [hvb] using hva)⟩

def Convex2 (a b : Vertex) : Vertex → Prop := fun v => PathAt v a b

theorem hull_pair_iff (a b v : Vertex) :
    Hull (fun x => x=a ∨ x=b) v ↔ PathAt v a b := by
  constructor
  · rintro ⟨x,y,hx,hy,hp⟩
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · have h := path_identical v a hp; subst v; exact PathAt.endpointL a b
    · exact hp
    · exact path_sym hp
    · have h := path_identical v b hp; subst v; exact PathAt.endpointR a b
  · intro hp; exact ⟨a,b,Or.inl rfl,Or.inr rfl,hp⟩

theorem path_convex (a b : Vertex) : Convex (Convex2 a b) := by
  intro v x y hx hy hp
  exact (hull_pair_iff a b v).1 (hull_convex (fun z => z=a ∨ z=b) v x y
    ((hull_pair_iff a b x).2 hx) ((hull_pair_iff a b y).2 hy) hp)

theorem convex_inter (A B : Vertex → Prop) (ha : Convex A) (hb : Convex B) :
    Convex (fun v => A v ∧ B v) := by
  intro v a b ha' hb' hp; exact ⟨ha v a b ha'.1 hb'.1 hp,hb v a b ha'.2 hb'.2 hp⟩

theorem helly_four (A B C D : Vertex → Prop)
    (ha : Convex A) (hb : Convex B) (hc : Convex C) (hd : Convex D)
    (hab : ∃v,A v∧B v) (hac : ∃v,A v∧C v) (had : ∃v,A v∧D v)
    (hbc : ∃v,B v∧C v) (hbd : ∃v,B v∧D v) (hcd : ∃v,C v∧D v) :
    ∃v,A v∧B v∧C v∧D v := by
  obtain ⟨x,hax,hbx,hcx⟩ := vertex_helly_three A B C ha hb hc hab hbc hac
  obtain ⟨y,hay,hby,hdy⟩ := vertex_helly_three A B D ha hb hd hab hbd had
  obtain ⟨v,⟨hav,hbv⟩,hcv,hdv⟩ := vertex_helly_three (fun v => A v∧B v) C D
    (convex_inter A B ha hb) hc hd ⟨x,⟨hax,hbx⟩,hcx⟩ hcd ⟨y,⟨hay,hby⟩,hdy⟩
  exact ⟨v,hav,hbv,hcv,hdv⟩
end PairGeometry
