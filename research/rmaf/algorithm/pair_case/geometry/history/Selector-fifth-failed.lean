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
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst x <;> subst y
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

namespace PairGeometry
open VertexGeometry

def Realized (S : Vertex → Prop) (v : Vertex) (r : Nat) : Prop :=
  ∃ a, S a ∧ region v a = r

def Three (S : Vertex → Prop) (v : Vertex) : Prop :=
  ∀ r, r < 3 → Realized S v r

def NoSharedLabels (S T : Vertex → Prop) : Prop :=
  ∀ v, Hull S v → Hull T v → ¬S v ∧ ¬T v

def IsSide (p : Vertex) (s inside : Bool) (a : Vertex) : Prop :=
  if inside then Prefix (p++[s]) a else ¬Prefix (p++[s]) a

def Sector (S : Vertex → Prop) (p : Vertex) (s inside : Bool) : Vertex → Prop :=
  fun a => S a ∧ IsSide p s inside a

theorem opposite_path (p : Vertex) (s inside : Bool) (a b : Vertex)
    (ha : IsSide p s inside a) (hb : IsSide p s (!inside) b) : PathAt p a b := by
  cases inside with
  | false => exact path_sym (edge_cross_path p s b a hb ha).1
  | true => exact (edge_cross_path p s a b ha hb).1

theorem three_of_sector_collision (S T : Vertex → Prop) (p : Vertex) (s inside : Bool)
    (hn : NoSharedLabels S T) (htp : Hull T p)
    (hopp : ∃ c, S c ∧ IsSide p s (!inside) c)
    (hbad : ∃ w, Hull (Sector S p s inside) w ∧ Hull T w) :
    ∃ m, Hull S m ∧ Hull T m ∧ Three S m := by
  obtain ⟨w,⟨a,b,⟨hsa,ha⟩,⟨hsb,hb⟩,hw⟩,htw⟩ := hbad
  obtain ⟨c,hsc,hc⟩ := hopp
  have hpa := opposite_path p s inside a c ha hc
  have hpb := opposite_path p s inside b c hb hc
  obtain ⟨m,htm,hmab,hmac,hmbc⟩ := helly_four (Hull T)
    (Convex2 a b) (Convex2 a c) (Convex2 b c)
    (hull_convex T) (path_convex a b) (path_convex a c) (path_convex b c)
    ⟨w,htw,hw⟩ ⟨p,htp,hpa⟩ ⟨p,htp,hpb⟩
    ⟨a,PathAt.endpointL a b,PathAt.endpointL a c⟩
    ⟨b,PathAt.endpointR a b,PathAt.endpointL b c⟩
    ⟨c,PathAt.endpointR a c,PathAt.endpointR b c⟩
  have hsm : Hull S m := ⟨a,b,hsa,hsb,hmab⟩
  have hnl := (hn m hsm htm).1
  have ham : a ≠ m := by intro e; subst a; exact hnl hsa
  have hbm : b ≠ m := by intro e; subst b; exact hnl hsb
  have hcm : c ≠ m := by intro e; subst c; exact hnl hsc
  have hra := nonlabel_region_lt_three m a ham
  have hrb := nonlabel_region_lt_three m b hbm
  have hrc := nonlabel_region_lt_three m c hcm
  have hab := path_region_ne m a b hmab ham hbm
  have hac := path_region_ne m a c hmac ham hcm
  have hbc := path_region_ne m b c hmbc hbm hcm
  refine ⟨m,hsm,htm,?_⟩
  intro r hr
  have hh : r=region m a ∨ r=region m b ∨ r=region m c := by omega
  rcases hh with h | h | h
  · exact ⟨a,hsa,h.symm⟩
  · exact ⟨b,hsb,h.symm⟩
  · exact ⟨c,hsc,h.symm⟩

theorem other_direction (S : Vertex → Prop) (v : Vertex) (r : Nat)
    (hn : ¬S v) (hv : Hull S v) : ∃ b, S b ∧ region v b ≠ r := by
  obtain ⟨a,b,ha,hb,hra,hrb,hab⟩ := occupied_nonlabel_two_directions S v hn hv
  by_cases h : region v a = r
  · exact ⟨b,hb,by intro e; exact hab (h.trans e.symm)⟩
  · exact ⟨a,ha,h⟩

theorem child_hull_of_realized (S : Vertex → Prop) (v : Vertex) (s : Bool)
    (hn : ¬S v) (hv : Hull S v) (hr : Realized S v (side s)) :
    Hull S (v++[s]) := by
  obtain ⟨a,ha,har⟩ := hr
  obtain ⟨b,hb,hbr⟩ := other_direction S v (side s) hn hv
  have hpa := (region_child_iff v a s).1 har
  have hpb : ¬Prefix (v++[s]) b := by simpa [← region_child_iff] using hbr
  exact ⟨a,b,ha,hb,(edge_cross_path v s a b hpa hpb).2⟩

theorem parent_hull_of_realized (S : Vertex → Prop) (p : Vertex) (s : Bool)
    (hn : ¬S (p++[s])) (hv : Hull S (p++[s])) (hr : Realized S (p++[s]) 2) :
    Hull S p := by
  obtain ⟨a,ha,har⟩ := hr
  obtain ⟨b,hb,hbr⟩ := other_direction S (p++[s]) 2 hn hv
  have hpa : ¬Prefix (p++[s]) a := (region_up_iff _ _).1 har
  have hpb : Prefix (p++[s]) b := by
    by_cases h : Prefix (p++[s]) b
    · exact h
    · exact False.elim (hbr ((region_up_iff _ _).2 h))
  exact ⟨b,a,hb,ha,(edge_cross_path p s b a hpb hpa).1⟩

theorem split_last (v : Vertex) (hn : v ≠ []) : ∃ p s, v=p++[s] := by
  induction v with
  | nil => exact False.elim (hn rfl)
  | cons s v ih =>
    by_cases h : v=[]
    · subst v; exact ⟨[],s,rfl⟩
    · obtain ⟨p,t,hp⟩ := ih h
      exact ⟨s::p,t,by simp [hp]⟩

theorem common_direction (S T : Vertex → Prop) (v : Vertex)
    (hs : ¬S v) (ht : ¬T v) (hsv : Hull S v) (htv : Hull T v) :
    ∃ r, r<3 ∧ Realized S v r ∧ Realized T v r := by
  obtain ⟨a,b,ha,hb,hra,hrb,hab⟩ := occupied_nonlabel_two_directions S v hs hsv
  obtain ⟨c,d,hc,hd,hrc,hrd,hcd⟩ := occupied_nonlabel_two_directions T v ht htv
  have hh : region v a=region v c ∨ region v a=region v d ∨
      region v b=region v c ∨ region v b=region v d := by omega
  rcases hh with h | h | h | h
  · exact ⟨region v a,hra,⟨a,ha,rfl⟩,⟨c,hc,h.symm⟩⟩
  · exact ⟨region v a,hra,⟨a,ha,rfl⟩,⟨d,hd,h.symm⟩⟩
  · exact ⟨region v b,hrb,⟨b,hb,rfl⟩,⟨c,hc,h.symm⟩⟩
  · exact ⟨region v b,hrb,⟨b,hb,rfl⟩,⟨d,hd,h.symm⟩⟩

theorem shared_edge (S T : Vertex → Prop) (hn : NoSharedLabels S T)
    (hover : ∃ v, Hull S v ∧ Hull T v) :
    ∃ p s, Hull S p ∧ Hull T p ∧ Hull S (p++[s]) ∧ Hull T (p++[s]) := by
  obtain ⟨v,hsv,htv⟩ := hover
  obtain ⟨hs,ht⟩ := hn v hsv htv
  obtain ⟨r,hr,hsr,htr⟩ := common_direction S T v hs ht hsv htv
  have hcases : r=0 ∨ r=1 ∨ r=2 := by omega
  rcases hcases with h | h | h
  · subst r
    exact ⟨v,false,hsv,htv,child_hull_of_realized S v false hs hsv hsr,
      child_hull_of_realized T v false ht htv htr⟩
  · subst r
    exact ⟨v,true,hsv,htv,child_hull_of_realized S v true hs hsv hsr,
      child_hull_of_realized T v true ht htv htr⟩
  · subst r
    have hv : v ≠ [] := by
      intro e; subst v
      obtain ⟨a,ha,hra⟩ := hsr
      exact region_root_not_up a hra
    obtain ⟨p,s,hp⟩ := split_last v hv
    subst v
    exact ⟨p,s,parent_hull_of_realized S p s hs hsv hsr,
      parent_hull_of_realized T p s ht htv htr,hsv,htv⟩

theorem edge_nonempty_sides (S : Vertex → Prop) (p : Vertex) (s : Bool)
    (hn : ¬S p) (hp : Hull S p) (hv : Hull S (p++[s])) :
    (∃ a,S a∧Prefix (p++[s]) a) ∧ (∃ b,S b∧¬Prefix (p++[s]) b) := by
  classical
  constructor
  · obtain ⟨a,ha,hpath⟩ := hull_subset_reach S (p++[s]) hv
    refine ⟨a,ha,?_⟩
    by_cases h : Prefix (p++[s]) a
    · exact h
    · exact False.elim (path_to_root_not_up _ _ _ hpath rfl ((region_up_iff _ _).2 h))
  · by_cases h : ∃ b,S b∧¬Prefix (p++[s]) b
    · exact h
    have hall : ∀ a,S a→Prefix (p++[s]) a := by
      intro a ha
      by_cases hh : Prefix (p++[s]) a
      · exact hh
      · exact False.elim (h ⟨a,ha,hh⟩)
    obtain ⟨a,b,ha,hb,hpath⟩ := hp
    have ham : a≠p := by intro e; subst a; exact hn ha
    have hbm : b≠p := by intro e; subst b; exact hn hb
    exact False.elim (path_region_ne p a b hpath ham hbm
      (((region_child_iff p a s).2 (hall a ha)).trans
        ((region_child_iff p b s).2 (hall b hb)).symm))
end PairGeometry

namespace PairGeometry
open VertexGeometry

def SharedThree (S T : Vertex → Prop) : Prop :=
  ∃v,Hull S v∧Hull T v∧(Three S v∨Three T v)

def ClearEdge (S T : Vertex → Prop) (p : Vertex) (s : Bool) : Prop :=
  (∀ inside w,Hull (Sector S p s inside) w→¬Hull T w) ∧
  (∀ inside w,Hull (Sector T p s inside) w→¬Hull S w)

theorem address_selector (S T : Vertex → Prop) (hn : NoSharedLabels S T)
    (hover : ∃v,Hull S v∧Hull T v) :
    SharedThree S T ∨ ∃p s,Hull S p∧Hull T p∧Hull S (p++[s])∧Hull T (p++[s])∧
      (∀inside,Nonempty (Sector S p s inside))∧
      (∀inside,Nonempty (Sector T p s inside))∧ClearEdge S T p s := by
  classical
  by_cases hthree : SharedThree S T
  · exact Or.inl hthree
  · apply Or.inr
    obtain ⟨p,s,hsp,htp,hsv,htv⟩ := shared_edge S T hn hover
    obtain ⟨hsi,hso⟩ := edge_nonempty_sides S p s (hn p hsp htp).1 hsp hsv
    obtain ⟨hti,hto⟩ := edge_nonempty_sides T p s (hn p hsp htp).2 htp htv
    have hsides : ∀inside,Nonempty (Sector S p s inside) := by
      intro inside; cases inside
      · exact hso
      · exact hsi
    have htides : ∀inside,Nonempty (Sector T p s inside) := by
      intro inside; cases inside
      · exact hto
      · exact hti
    refine ⟨p,s,hsp,htp,hsv,htv,hsides,htides,?_,?_⟩
    · intro inside w hsw htw
      obtain ⟨m,hsm,htm,h3⟩ := three_of_sector_collision S T p s inside hn htp
        (hsides (!inside)) ⟨w,hsw,htw⟩
      exact hthree ⟨m,hsm,htm,Or.inl h3⟩
    · intro inside w htw hsw
      have hns : NoSharedLabels T S := fun v ht hs => ⟨(hn v hs ht).2,(hn v hs ht).1⟩
      obtain ⟨m,htm,hsm,h3⟩ := three_of_sector_collision T S p s inside hns hsp
        (htides (!inside)) ⟨w,htw,hsw⟩
      exact hthree ⟨m,hsm,htm,Or.inr h3⟩

def vertices : RMAF.Tree → List Vertex
  | .leaf _ => [[]]
  | .node l r => [] :: (RMAF.prependSide false (vertices l) ++ RMAF.prependSide true (vertices r))

def edges : RMAF.Tree → List (Vertex × Vertex)
  | .leaf _ => []
  | .node l r => ([],[false]) :: ([],[true]) ::
      ((edges l).map (fun e => (false::e.1,false::e.2)) ++
       (edges r).map (fun e => (true::e.1,true::e.2)))

theorem rootspan_vertices (D : List Nat) (t : RMAF.Tree) :
    ∀v,v∈RMAF.rootedSpan D t→v∈vertices t := by
  induction t with
  | leaf x => intro v hv; simp only [RMAF.rootedSpan] at hv; split at hv <;> simp_all [vertices]
  | node l r il ir =>
    intro v hv
    cases v with
    | nil => simp [vertices]
    | cons s v =>
      cases s with
      | false =>
        simp only [RMAF.rootedSpan] at hv
        split at hv
        · simp at hv
        · have h : v∈RMAF.rootedSpan D l := by simpa [RMAF.prependSide] using hv
          simpa [vertices,RMAF.prependSide] using il v h
      | true =>
        simp only [RMAF.rootedSpan] at hv
        split at hv
        · simp at hv
        · have h : v∈RMAF.rootedSpan D r := by simpa [RMAF.prependSide] using hv
          simpa [vertices,RMAF.prependSide] using ir v h

theorem minimal_vertices (D : List Nat) (t : RMAF.Tree) :
    ∀v,v∈RMAF.minimalVertices D t→v∈vertices t := by
  induction t with
  | leaf x => intro v hv; simp only [RMAF.minimalVertices] at hv; split at hv <;> simp_all [vertices]
  | node l r il ir =>
    intro v hv
    cases v with
    | nil => simp [vertices]
    | cons s v =>
      cases s with
      | false =>
        simp only [RMAF.minimalVertices] at hv
        split at hv
        · simp [RMAF.prependSide] at hv
        · split at hv
          · have h : v∈RMAF.minimalVertices D l := by simpa [RMAF.prependSide] using hv
            simpa [vertices,RMAF.prependSide] using il v h
          · have h : v∈RMAF.rootedSpan D l := by simpa [RMAF.prependSide] using hv
            simpa [vertices,RMAF.prependSide] using rootspan_vertices D l v h
      | true =>
        simp only [RMAF.minimalVertices] at hv
        split at hv
        · have h : v∈RMAF.minimalVertices D r := by simpa [RMAF.prependSide] using hv
          simpa [vertices,RMAF.prependSide] using ir v h
        · split at hv
          · simp [RMAF.prependSide] at hv
          · have h : v∈RMAF.rootedSpan D r := by simpa [RMAF.prependSide] using hv
            simpa [vertices,RMAF.prependSide] using rootspan_vertices D r v h

theorem child_actual_edge (t : RMAF.Tree) (p : Vertex) (s : Bool)
    (hv : p++[s]∈vertices t) : (p,p++[s])∈edges t := by
  induction p generalizing t with
  | nil =>
    cases t with
    | leaf x => simp [vertices] at hv
    | node l r => cases s <;> simp [edges]
  | cons b p ih =>
    cases t with
    | leaf x => simp [vertices] at hv
    | node l r =>
      cases b with
      | false =>
        have hh : p++[s]∈vertices l := by simpa [vertices,RMAF.prependSide] using hv
        have he := ih l hh
        simp only [edges,List.mem_cons,List.mem_append,List.mem_map]
        exact Or.inr (Or.inr (Or.inl ⟨(p,p++[s]),he,rfl⟩))
      | true =>
        have hh : p++[s]∈vertices r := by simpa [vertices,RMAF.prependSide] using hv
        have he := ih r hh
        simp only [edges,List.mem_cons,List.mem_append,List.mem_map]
        exact Or.inr (Or.inr (Or.inr ⟨(p,p++[s]),he,rfl⟩))
end PairGeometry

namespace PairGeometry
open VertexGeometry

def prefixB : Vertex → Vertex → Bool
  | [], _ => true
  | _::_, [] => false
  | s::p,t::a => (s==t) && prefixB p a

theorem prefixB_correct (p a : Vertex) : prefixB p a = true ↔ Prefix p a := by
  induction p generalizing a with
  | nil => simp [prefixB,prefix_nil]
  | cons s p ih => cases a with
    | nil => simp [prefixB,Prefix]
    | cons t a => simp [prefixB,prefix_cons,ih]

def leafAddress (t : RMAF.Tree) (x : Nat) : Vertex := (leafList [x] t).headD []

def descendants (t : RMAF.Tree) (v : Vertex) : List Nat :=
  (RMAF.leaves t).filter (fun x => prefixB v (leafAddress t x))

def sideLabels (A : List Nat) (t : RMAF.Tree) (v : Vertex) (inside : Bool) : List Nat :=
  A.filter (fun x => if inside then (descendants t v).contains x else !((descendants t v).contains x))

theorem leafAddress_correct (t : RMAF.Tree) (x : Nat) (hn : (RMAF.leaves t).Nodup)
    (a : Vertex) (ha : selectedLeaves [x] t a) : leafAddress t x = a := by
  have hm := (leafList_correct [x] t a).2 ha
  unfold leafAddress
  cases he : leafList [x] t with
  | nil => simp [he] at hm
  | cons b bs =>
    have hb := (leafList_correct [x] t b).1 (by simp [he])
    have hab := singleton_selected_address_unique t x hn b a hb ha
    simp [hab]

theorem descendants_mem (t : RMAF.Tree) (v : Vertex) (x : Nat) :
    x∈descendants t v ↔ x∈RMAF.leaves t ∧ Prefix v (leafAddress t x) := by
  simp [descendants,prefixB_correct]

theorem sideLabels_mem (A : List Nat) (t : RMAF.Tree) (v : Vertex) (inside : Bool) (x : Nat) :
    x∈sideLabels A t v inside ↔ x∈A ∧ (if inside then x∈descendants t v else x∉descendants t v) := by
  cases inside <;> simp [sideLabels]

theorem selected_side (A : List Nat) (t : RMAF.Tree) (p : Vertex) (s inside : Bool)
    (hn : (RMAF.leaves t).Nodup) (a : Vertex) :
    selectedLeaves (sideLabels A t (p++[s]) inside) t a ↔ Sector (selectedLeaves A t) p s inside a := by
  constructor
  · intro h
    obtain ⟨x,hx,ha⟩ := (selected_decompose_label _ t a).1 h
    obtain ⟨hxA,hxD⟩ := (sideLabels_mem A t (p++[s]) inside x).1 hx
    have hxl := (singleton_selected_exists t x).1 ⟨a,ha⟩
    have haddr := leafAddress_correct t x hn a ha
    refine ⟨(selected_decompose_label A t a).2 ⟨x,hxA,ha⟩,?_⟩
    cases inside with
    | false =>
      change ¬Prefix (p++[s]) a
      intro hp
      exact hxD ((descendants_mem t (p++[s]) x).2 ⟨hxl,by simpa [haddr] using hp⟩)
    | true =>
      change Prefix (p++[s]) a
      simpa [haddr] using ((descendants_mem t (p++[s]) x).1 hxD).2
  · rintro ⟨hA,hside⟩
    obtain ⟨x,hxA,ha⟩ := (selected_decompose_label A t a).1 hA
    have hxl := (singleton_selected_exists t x).1 ⟨a,ha⟩
    have haddr := leafAddress_correct t x hn a ha
    apply (selected_decompose_label _ t a).2
    refine ⟨x,(sideLabels_mem A t (p++[s]) inside x).2 ⟨hxA,?_⟩,ha⟩
    cases inside with
    | false =>
      intro hd
      exact hside (by simpa [haddr] using ((descendants_mem t (p++[s]) x).1 hd).2)
    | true => exact (descendants_mem t (p++[s]) x).2 ⟨hxl,by simpa [haddr] using hside⟩

theorem hull_congr (S T : Vertex → Prop) (h : ∀a,S a↔T a) (v : Vertex) : Hull S v↔Hull T v := by
  constructor <;> rintro ⟨a,b,ha,hb,hp⟩
  · exact ⟨a,b,(h a).1 ha,(h b).1 hb,hp⟩
  · exact ⟨a,b,(h a).2 ha,(h b).2 hb,hp⟩

theorem sector_hull_correct (A : List Nat) (t : RMAF.Tree) (p : Vertex) (s inside : Bool)
    (hn : (RMAF.leaves t).Nodup) (w : Vertex) :
    w∈RMAF.minimalVertices (sideLabels A t (p++[s]) inside) t ↔
      Hull (Sector (selectedLeaves A t) p s inside) w := by
  rw [minimalVertices_correct]
  exact hull_congr _ _ (selected_side A t p s inside hn) w

theorem regions_three (A : List Nat) (t : RMAF.Tree) (v : Vertex) :
    Three (selectedLeaves A t) v ↔ (regions A t v).length = 3 := by
  have hflags : (regions A t v).length=3 ↔
      0∈regions A t v ∧ 1∈regions A t v ∧ 2∈regions A t v := by
    unfold regions
    cases h0 : (leafList A t).any (fun a => region v a == 0) <;>
      cases h1 : (leafList A t).any (fun a => region v a == 1) <;>
      cases h2 : (leafList A t).any (fun a => region v a == 2) <;> simp [h0,h1,h2]
  rw [hflags]
  constructor
  · intro h
    exact ⟨(regionList_mem A t v 0).2 ⟨by decide,h 0 (by decide)⟩,
      (regionList_mem A t v 1).2 ⟨by decide,h 1 (by decide)⟩,
      (regionList_mem A t v 2).2 ⟨by decide,h 2 (by decide)⟩⟩
  · rintro ⟨h0,h1,h2⟩ r hr
    have hc : r=0∨r=1∨r=2 := by omega
    rcases hc with rfl | rfl | rfl
    · exact ((regionList_mem A t v 0).1 h0).2
    · exact ((regionList_mem A t v 1).1 h1).2
    · exact ((regionList_mem A t v 2).1 h2).2

def ActualClear (t : RMAF.Tree) (A B : List Nat) (v : Vertex) : Prop :=
  (∀inside w,w∈RMAF.minimalVertices (sideLabels A t v inside) t→w∉RMAF.minimalVertices B t) ∧
  (∀inside w,w∈RMAF.minimalVertices (sideLabels B t v inside) t→w∉RMAF.minimalVertices A t)

theorem actual_selector_exists (t : RMAF.Tree) (A B : List Nat)
    (hn : (RMAF.leaves t).Nodup) (hd : ∀x,x∈A→x∈B→False)
    (hover : ∃v,v∈RMAF.minimalVertices A t∧v∈RMAF.minimalVertices B t) :
    (∃v,v∈RMAF.minimalVertices A t∧v∈RMAF.minimalVertices B t∧
      ((regions A t v).length=3∨(regions B t v).length=3)) ∨
    ∃p s,(p,p++[s])∈edges t ∧ p∈RMAF.minimalVertices A t ∧ p∈RMAF.minimalVertices B t ∧
      (p++[s])∈RMAF.minimalVertices A t ∧ (p++[s])∈RMAF.minimalVertices B t ∧
      (∀inside,sideLabels A t (p++[s]) inside≠[]) ∧
      (∀inside,sideLabels B t (p++[s]) inside≠[]) ∧ActualClear t A B (p++[s]) := by
  have hnl : NoSharedLabels (selectedLeaves A t) (selectedLeaves B t) := by
    intro v ha hb
    exact disjoint_parent_overlap_nonlabel A B t v hd
      ((minimalVertices_correct A t v).2 ha) ((minimalVertices_correct B t v).2 hb)
  have hov : ∃v,Hull (selectedLeaves A t) v∧Hull (selectedLeaves B t) v := by
    simpa only [minimalVertices_correct] using hover
  rcases address_selector _ _ hnl hov with h3 | he
  · apply Or.inl
    obtain ⟨v,ha,hb,h3⟩ := h3
    refine ⟨v,(minimalVertices_correct _ _ _).2 ha,(minimalVertices_correct _ _ _).2 hb,?_⟩
    exact h3.imp ((regions_three A t v).1) ((regions_three B t v).1)
  · apply Or.inr
    obtain ⟨p,s,hap,hbp,hav,hbv,ha,hb,hclear⟩ := he
    have hav' := (minimalVertices_correct A t (p++[s])).2 hav
    refine ⟨p,s,child_actual_edge t p s (minimal_vertices A t _ hav'),
      (minimalVertices_correct _ _ _).2 hap,(minimalVertices_correct _ _ _).2 hbp,
      hav',(minimalVertices_correct _ _ _).2 hbv,?_,?_,?_,?_⟩
    · intro inside hnil
      obtain ⟨a,haa⟩ := ha inside
      have hs := (selected_side A t p s inside hn a).2 haa
      rw [hnil] at hs
      obtain ⟨x,hx,_⟩ := (selected_decompose_label [] t a).1 hs
      simp at hx
    · intro inside hnil
      obtain ⟨a,hba⟩ := hb inside
      have hs := (selected_side B t p s inside hn a).2 hba
      rw [hnil] at hs
      obtain ⟨x,hx,_⟩ := (selected_decompose_label [] t a).1 hs
      simp at hx
    · intro inside w hw hb'
      exact hclear.1 inside w ((sector_hull_correct A t p s inside hn w).1 hw)
        ((minimalVertices_correct B t w).1 hb')
    · intro inside w hw ha'
      exact hclear.2 inside w ((sector_hull_correct B t p s inside hn w).1 hw)
        ((minimalVertices_correct A t w).1 ha')
end PairGeometry
