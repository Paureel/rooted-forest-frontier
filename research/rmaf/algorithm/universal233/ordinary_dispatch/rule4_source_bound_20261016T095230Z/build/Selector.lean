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
    | true => exact (descendants_mem t (p++[s]) x).2 ⟨hxl,by simpa [haddr,IsSide] using hside⟩

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

namespace PairGeometry
open VertexGeometry

inductive Choice where
  | vertex : Vertex → Choice
  | edge : (Vertex × Vertex) → Choice
  deriving DecidableEq, Repr

def properInput (t : RMAF.Tree) (A B : List Nat) : Bool :=
  decide (RMAF.leaves t).Nodup && decide A.Nodup && decide B.Nodup &&
  !A.isEmpty && !B.isEmpty &&
  A.all (fun x => (RMAF.leaves t).contains x) &&
  B.all (fun x => (RMAF.leaves t).contains x) && A.all (fun x => !(B.contains x))

def vertexOK (t : RMAF.Tree) (A B : List Nat) (v : Vertex) : Bool :=
  (RMAF.minimalVertices A t).contains v && (RMAF.minimalVertices B t).contains v &&
    ((regions A t v).length==3 || (regions B t v).length==3)

def edgeOK (t : RMAF.Tree) (A B : List Nat) (e : Vertex × Vertex) : Bool :=
  (RMAF.minimalVertices A t).contains e.1 && (RMAF.minimalVertices B t).contains e.1 &&
  (RMAF.minimalVertices A t).contains e.2 && (RMAF.minimalVertices B t).contains e.2 &&
  [false,true].all (fun inside =>
    !(sideLabels A t e.2 inside).isEmpty && !(sideLabels B t e.2 inside).isEmpty &&
    RMAF.disjointVertices (RMAF.minimalVertices (sideLabels A t e.2 inside) t) (RMAF.minimalVertices B t) &&
    RMAF.disjointVertices (RMAF.minimalVertices (sideLabels B t e.2 inside) t) (RMAF.minimalVertices A t))

def choose (t : RMAF.Tree) (A B : List Nat) : Option Choice :=
  if properInput t A B then
    match (vertices t).find? (vertexOK t A B) with
    | some v => some (.vertex v)
    | none => ((edges t).find? (edgeOK t A B)).map Choice.edge
  else none

def ValidChoice (t : RMAF.Tree) (A B : List Nat) : Choice → Prop
  | .vertex v => v∈RMAF.minimalVertices A t ∧ v∈RMAF.minimalVertices B t ∧
      ((regions A t v).length=3∨(regions B t v).length=3)
  | .edge e => e∈edges t ∧ e.1∈RMAF.minimalVertices A t ∧ e.1∈RMAF.minimalVertices B t ∧
      e.2∈RMAF.minimalVertices A t ∧ e.2∈RMAF.minimalVertices B t ∧
      (∀inside,sideLabels A t e.2 inside≠[]) ∧
      (∀inside,sideLabels B t e.2 inside≠[]) ∧ActualClear t A B e.2

theorem proper_nodup (t : RMAF.Tree) (A B : List Nat) (h : properInput t A B=true) :
    (RMAF.leaves t).Nodup := by
  simp only [properInput,Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1.1.1.1.1.1

theorem proper_disjoint (t : RMAF.Tree) (A B : List Nat) (h : properInput t A B=true) :
    ∀x,x∈A→x∈B→False := by
  simp only [properInput,Bool.and_eq_true] at h
  have ha : A.all (fun x => !(B.contains x))=true := h.2
  simpa using ha

theorem vertexOK_correct (t : RMAF.Tree) (A B : List Nat) (v : Vertex) :
    vertexOK t A B v=true ↔ ValidChoice t A B (.vertex v) := by
  simp [vertexOK,ValidChoice,and_assoc]

theorem disjointB_correct (L M : List Vertex) :
    RMAF.disjointVertices L M=true ↔ ∀w,w∈L→w∉M := by
  simp [RMAF.disjointVertices]

theorem edgeOK_correct (t : RMAF.Tree) (A B : List Nat) (e : Vertex × Vertex) :
    edgeOK t A B e=true ↔ e.1∈RMAF.minimalVertices A t ∧ e.1∈RMAF.minimalVertices B t ∧
      e.2∈RMAF.minimalVertices A t ∧ e.2∈RMAF.minimalVertices B t ∧
      (∀inside,sideLabels A t e.2 inside≠[]) ∧
      (∀inside,sideLabels B t e.2 inside≠[]) ∧ActualClear t A B e.2 := by
  simp only [edgeOK,Bool.and_eq_true,List.contains_eq_mem,decide_eq_true_eq]
  rw [List.all_eq_true]
  simp only [List.mem_cons,List.mem_singleton]
  constructor
  · rintro ⟨⟨⟨⟨ha,hb⟩,hc⟩,hd⟩,hall⟩
    have h (inside : Bool) := hall inside (by cases inside <;> simp)
    simp only [Bool.and_eq_true] at h
    refine ⟨ha,hb,hc,hd,?_,?_,?_,?_⟩
    · intro inside; have hh := (h inside).1.1.1; simpa using hh
    · intro inside; have hh := (h inside).1.1.2; simpa using hh
    · intro inside; exact (disjointB_correct _ _).1 (h inside).1.2
    · intro inside; exact (disjointB_correct _ _).1 (h inside).2
  · rintro ⟨ha,hb,hc,hd,hA,hB,hC,hD⟩
    refine ⟨⟨⟨⟨ha,hb⟩,hc⟩,hd⟩,?_⟩
    intro inside _
    have ha : !(sideLabels A t e.2 inside).isEmpty=true := by simpa using hA inside
    have hb : !(sideLabels B t e.2 inside).isEmpty=true := by simpa using hB inside
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨ha,hb⟩,(disjointB_correct _ _).2 (hC inside)⟩,
      (disjointB_correct _ _).2 (hD inside)⟩

theorem choose_sound (t : RMAF.Tree) (A B : List Nat) (o : Choice)
    (h : choose t A B=some o) : properInput t A B=true ∧ ValidChoice t A B o := by
  unfold choose at h
  split at h
  · rename_i hp
    refine ⟨hp,?_⟩
    split at h
    · rename_i v hv
      have ho : o=Choice.vertex v := by simpa using h.symm
      subst o
      exact (vertexOK_correct _ _ _ _).1 (List.find?_some hv)
    · rename_i hv
      cases he : (edges t).find? (edgeOK t A B) with
      | none => simp [he] at h
      | some e =>
        have ho : o=Choice.edge e := by simpa [he] using h.symm
        subst o
        exact ⟨List.mem_of_find?_eq_some he,(edgeOK_correct _ _ _ _).1 (List.find?_some he)⟩
  · simp at h

theorem choose_complete (t : RMAF.Tree) (A B : List Nat) (hp : properInput t A B=true)
    (hover : ∃v,v∈RMAF.minimalVertices A t∧v∈RMAF.minimalVertices B t) :
    ∃o,choose t A B=some o ∧ ValidChoice t A B o := by
  have hn := proper_nodup t A B hp
  have hd := proper_disjoint t A B hp
  have hex := actual_selector_exists t A B hn hd hover
  cases hvertex : (vertices t).find? (vertexOK t A B) with
  | some v =>
    have hc : choose t A B=some (.vertex v) := by simp [choose,hp,hvertex]
    exact ⟨.vertex v,hc,(choose_sound t A B _ hc).2⟩
  | none =>
    have hnone := (List.find?_eq_none).1 hvertex
    have hedge : ∃e,e∈edges t ∧ edgeOK t A B e=true := by
      rcases hex with h3 | he
      · obtain ⟨v,ha,hb,h3⟩ := h3
        exact False.elim (hnone v (minimal_vertices A t v ha)
          ((vertexOK_correct t A B v).2 ⟨ha,hb,h3⟩))
      · obtain ⟨p,s,he,ha,hb,hc,hd,hA,hB,hclear⟩ := he
        exact ⟨(p,p++[s]),he,(edgeOK_correct _ _ _ _).2 ⟨ha,hb,hc,hd,hA,hB,hclear⟩⟩
    have hsome := (List.find?_isSome).2 hedge
    cases he : (edges t).find? (edgeOK t A B) with
    | none => simp [he] at hsome
    | some e =>
      have hc : choose t A B=some (.edge e) := by simp [choose,hp,hvertex,he]
      exact ⟨.edge e,hc,(choose_sound t A B _ hc).2⟩
end PairGeometry

namespace PairGeometry
open VertexGeometry

def neighbor (v : Vertex) : Nat → Option Vertex
  | 0 => some (v++[false])
  | 1 => some (v++[true])
  | 2 => if v=[] then none else some v.dropLast
  | _ => none

theorem child_realized_of_hull (S : Vertex → Prop) (p : Vertex) (s : Bool)
    (hv : Hull S (p++[s])) : Realized S p (side s) := by
  classical
  obtain ⟨a,ha,hpath⟩ := hull_subset_reach S (p++[s]) hv
  have hpre : Prefix (p++[s]) a := by
    by_cases h : Prefix (p++[s]) a
    · exact h
    · exact False.elim (path_to_root_not_up _ _ _ hpath rfl ((region_up_iff _ _).2 h))
  exact ⟨a,ha,(region_child_iff p a s).2 hpre⟩

theorem prefix_child_ne (p : Vertex) (s : Bool) (a : Vertex) (ha : Prefix (p++[s]) a) : a≠p := by
  obtain ⟨q,hq⟩ := ha
  have hlen : a.length=p.length+1+q.length := by simp [hq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  intro h; rw [h] at hlen; omega

theorem up_realized_of_hull (S : Vertex → Prop) (p : Vertex) (s : Bool)
    (hp : Hull S p) : Realized S (p++[s]) 2 := by
  classical
  obtain ⟨a,b,ha,hb,hpath⟩ := hp
  by_cases hpa : Prefix (p++[s]) a
  · by_cases hpb : Prefix (p++[s]) b
    · exact False.elim (path_region_ne p a b hpath (prefix_child_ne p s a hpa)
        (prefix_child_ne p s b hpb)
        (((region_child_iff p a s).2 hpa).trans ((region_child_iff p b s).2 hpb).symm))
    · exact ⟨b,hb,(region_up_iff _ _).2 hpb⟩
  · exact ⟨a,ha,(region_up_iff _ _).2 hpa⟩

theorem realized_neighbor (S : Vertex → Prop) (v : Vertex) (r : Nat)
    (hr : r<3) (hn : ¬S v) (hv : Hull S v) :
    Realized S v r ↔ ∃w,neighbor v r=some w ∧ Hull S w := by
  classical
  have hc : r=0∨r=1∨r=2 := by omega
  rcases hc with rfl | rfl | rfl
  · constructor
    · intro h; exact ⟨v++[false],rfl,child_hull_of_realized S v false hn hv h⟩
    · rintro ⟨w,hw,hh⟩
      have he : w=v++[false] := by simpa [neighbor] using hw.symm
      subst w; exact child_realized_of_hull S v false hh
  · constructor
    · intro h; exact ⟨v++[true],rfl,child_hull_of_realized S v true hn hv h⟩
    · rintro ⟨w,hw,hh⟩
      have he : w=v++[true] := by simpa [neighbor] using hw.symm
      subst w; exact child_realized_of_hull S v true hh
  · by_cases he : v=[]
    · subst v
      constructor
      · rintro ⟨a,ha,hh⟩; exact False.elim (region_root_not_up a hh)
      · simp [neighbor]
    · obtain ⟨p,s,hp⟩ := split_last v he
      subst v
      have hd : (p++[s]).dropLast=p := by simp
      have hn0 : p++[s]≠[] := by simp
      constructor
      · intro h
        exact ⟨p,by simp [neighbor,hn0,hd],parent_hull_of_realized S p s hn hv h⟩
      · rintro ⟨w,hw,hh⟩
        have he : w=p := by simpa [neighbor,hn0,hd] using hw.symm
        subst w; exact up_realized_of_hull S p s hh

def neighborFlag (t : RMAF.Tree) (A : List Nat) (v : Vertex) (r : Nat) : Bool :=
  match neighbor v r with
  | none => false
  | some w => (RMAF.minimalVertices A t).contains w

def hullDirections (t : RMAF.Tree) (A : List Nat) (v : Vertex) : List Nat :=
  [0,1,2].filter (neighborFlag t A v)

def neighbors (v : Vertex) : List Vertex :=
  [v++[false],v++[true]] ++ (if v=[] then [] else [v.dropLast])

def hullNeighbors (t : RMAF.Tree) (A : List Nat) (v : Vertex) : List Vertex :=
  (neighbors v).filter (fun w => (RMAF.minimalVertices A t).contains w)

def hullDegree (t : RMAF.Tree) (A : List Nat) (v : Vertex) : Nat :=
  (hullNeighbors t A v).length

theorem neighborFlag_correct (t : RMAF.Tree) (A : List Nat) (v : Vertex) (r : Nat) :
    neighborFlag t A v r=true ↔ ∃w,neighbor v r=some w ∧ w∈RMAF.minimalVertices A t := by
  cases he : neighbor v r <;> simp [neighborFlag,he]

theorem regions_hullDirections (t : RMAF.Tree) (A : List Nat) (v : Vertex)
    (hn : ¬selectedLeaves A t v) (hv : v∈RMAF.minimalVertices A t) :
    regions A t v=hullDirections t A v := by
  unfold regions hullDirections
  apply List.filter_congr
  intro r hr
  have hr3 : r<3 := by simp at hr; omega
  apply Bool.eq_iff_iff.mpr
  calc
    ((leafList A t).any (fun a => region v a==r)=true) ↔ Realized (selectedLeaves A t) v r := by
      simp [Realized,List.any_eq_true,leafList_correct]
    _ ↔ ∃w,neighbor v r=some w∧Hull (selectedLeaves A t) w :=
      realized_neighbor _ v r hr3 hn ((minimalVertices_correct A t v).1 hv)
    _ ↔ ∃w,neighbor v r=some w∧w∈RMAF.minimalVertices A t := by
      simp only [minimalVertices_correct]
    _ ↔ neighborFlag t A v r=true := (neighborFlag_correct t A v r).symm

theorem direction_degree (t : RMAF.Tree) (A : List Nat) (v : Vertex) :
    (hullDirections t A v).length=hullDegree t A v := by
  unfold hullDirections hullDegree hullNeighbors neighbors neighborFlag
  by_cases hv : v=[]
  · subst v
    cases h0 : (RMAF.minimalVertices A t).contains [false] <;>
      cases h1 : (RMAF.minimalVertices A t).contains [true] <;> simp only [neighbor,h0,h1,List.filter_cons,List.filter_nil,List.length_cons,List.length_nil,List.nil_append,List.cons_append,Bool.false_eq_true,ite_false,ite_true]
  · cases h0 : (RMAF.minimalVertices A t).contains (v++[false]) <;>
      cases h1 : (RMAF.minimalVertices A t).contains (v++[true]) <;>
      cases h2 : (RMAF.minimalVertices A t).contains v.dropLast <;> simp only [neighbor,hv,h0,h1,h2,List.filter_cons,List.filter_nil,List.length_cons,List.length_nil,List.nil_append,List.cons_append,Bool.false_eq_true,ite_false,ite_true]

theorem region_count_actual_hull_degree (t : RMAF.Tree) (A : List Nat) (v : Vertex)
    (hn : ¬selectedLeaves A t v) (hv : v∈RMAF.minimalVertices A t) :
    (regions A t v).length=hullDegree t A v := by
  rw [regions_hullDirections t A v hn hv]
  exact direction_degree t A v

theorem child_ne_dropLast (v : Vertex) (s : Bool) : v++[s]≠v.dropLast := by
  intro h
  have hh := congrArg List.length h
  simp [List.length_dropLast] at hh
  omega

theorem neighbors_nodup (v : Vertex) : (neighbors v).Nodup := by
  by_cases hv : v=[]
  · subst v; decide
  · simp [neighbors,hv,child_ne_dropLast]

theorem neighbors_mem (v w : Vertex) :
    w∈neighbors v ↔ (∃s,w=v++[s]) ∨ (∃s,v=w++[s]) := by
  classical
  constructor
  · intro hw
    simp only [neighbors,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with (h|h) | h
    · exact Or.inl ⟨false,h⟩
    · exact Or.inl ⟨true,h⟩
    · by_cases hv : v=[]
      · simp [hv] at h
      · have hwp : w=v.dropLast := by simpa [hv] using h
        obtain ⟨p,s,hp⟩ := split_last v hv
        subst v
        have he : w=p := by simpa using hwp
        exact Or.inr ⟨s,by simp [he]⟩
  · rintro (⟨s,rfl⟩|⟨s,rfl⟩)
    · cases s <;> simp [neighbors]
    · simp [neighbors]

def ActualAdjacent (t : RMAF.Tree) (v w : Vertex) : Prop :=
  (v,w)∈edges t ∨ (w,v)∈edges t

theorem edges_shape (t : RMAF.Tree) : ∀e,e∈edges t→∃p s,e=(p,p++[s]) := by
  induction t with
  | leaf x => intro e he; simp [edges] at he
  | node l r il ir =>
    intro e he
    simp only [edges,List.mem_cons,List.mem_append,List.mem_map] at he
    rcases he with h|h|h|h
    · subst e; exact ⟨[],false,rfl⟩
    · subst e; exact ⟨[],true,rfl⟩
    · obtain ⟨f,hf,rfl⟩ := h
      obtain ⟨p,s,rfl⟩ := il f hf
      exact ⟨false::p,s,rfl⟩
    · obtain ⟨f,hf,rfl⟩ := h
      obtain ⟨p,s,rfl⟩ := ir f hf
      exact ⟨true::p,s,rfl⟩

theorem hullNeighbors_actual (t : RMAF.Tree) (A : List Nat) (v : Vertex)
    (hv : v∈RMAF.minimalVertices A t) (w : Vertex) :
    w∈hullNeighbors t A v ↔ w∈RMAF.minimalVertices A t∧ActualAdjacent t v w := by
  constructor
  · intro h
    obtain ⟨hw,hm⟩ := List.mem_filter.1 h
    have hm' : w∈RMAF.minimalVertices A t := by simpa using hm
    refine ⟨hm',?_⟩
    rcases (neighbors_mem v w).1 hw with ⟨s,he⟩|⟨s,he⟩
    · subst w
      exact Or.inl (child_actual_edge t v s (minimal_vertices A t _ hm'))
    · subst v
      exact Or.inr (child_actual_edge t w s (minimal_vertices A t _ hv))
  · rintro ⟨hw,he⟩
    apply List.mem_filter.2
    refine ⟨?_,by simpa using hw⟩
    apply (neighbors_mem v w).2
    rcases he with he|he
    · obtain ⟨p,s,hp⟩ := edges_shape t (v,w) he
      have h := Prod.mk.inj hp
      exact Or.inl ⟨s,by simpa [h.1] using h.2⟩
    · obtain ⟨p,s,hp⟩ := edges_shape t (w,v) he
      have h := Prod.mk.inj hp
      exact Or.inr ⟨s,by simpa [h.1] using h.2⟩

theorem hullNeighbors_nodup (t : RMAF.Tree) (A : List Nat) (v : Vertex) :
    (hullNeighbors t A v).Nodup := by
  exact List.Pairwise.filter _ (neighbors_nodup v)
end PairGeometry

namespace PairGeometry
open VertexGeometry

def findCalls (p : α → Bool) : List α → Nat
  | [] => 0
  | x::xs => if p x then 1 else 1+findCalls p xs

theorem findCalls_bound (p : α → Bool) (xs : List α) : findCalls p xs≤xs.length := by
  induction xs with
  | nil => simp [findCalls]
  | cons x xs ih => unfold findCalls; split <;> simp_all <;> omega

def chooseCalls (t : RMAF.Tree) (A B : List Nat) : Nat :=
  if properInput t A B then
    findCalls (vertexOK t A B) (vertices t) +
    (if (vertices t).find? (vertexOK t A B)=none then findCalls (edgeOK t A B) (edges t) else 0)
  else 0

theorem vertices_length (t : RMAF.Tree) : (vertices t).length+1=2*(RMAF.leaves t).length := by
  induction t with
  | leaf x => rfl
  | node l r il ir =>
    simp only [vertices,RMAF.leaves,List.length_cons,List.length_append,RMAF.prependSide,List.length_map]
    omega

theorem edges_length (t : RMAF.Tree) : (edges t).length+1=(vertices t).length := by
  induction t with
  | leaf x => rfl
  | node l r il ir =>
    simp only [edges,vertices,List.length_cons,List.length_append,RMAF.prependSide,List.length_map]
    omega

theorem chooseCalls_bound (t : RMAF.Tree) (A B : List Nat) :
    chooseCalls t A B≤(vertices t).length+(edges t).length := by
  unfold chooseCalls
  split
  · have hv := findCalls_bound (vertexOK t A B) (vertices t)
    have he := findCalls_bound (edgeOK t A B) (edges t)
    split <;> omega
  · omega

theorem chooseCalls_linear (t : RMAF.Tree) (A B : List Nat) :
    chooseCalls t A B+3≤4*(RMAF.leaves t).length := by
  have h := chooseCalls_bound t A B
  have hv := vertices_length t
  have he := edges_length t
  omega
end PairGeometry

namespace PairGeometry
open VertexGeometry

theorem choose_binary_when_two (t : RMAF.Tree) (A B : List Nat)
    (hp : properInput t A B=true)
    (hover : ∃v,v∈RMAF.minimalVertices A t∧v∈RMAF.minimalVertices B t)
    (htwo : ∀v,v∈RMAF.minimalVertices A t→v∈RMAF.minimalVertices B t→
      (regions A t v).length=2∧(regions B t v).length=2) :
    ∃e,choose t A B=some (.edge e) ∧ ValidChoice t A B (.edge e) := by
  obtain ⟨o,ho,hv⟩ := choose_complete t A B hp hover
  cases o with
  | edge e => exact ⟨e,ho,hv⟩
  | vertex v =>
    obtain ⟨ha,hb,h3⟩ := hv
    obtain ⟨h2a,h2b⟩ := htwo v ha hb
    rcases h3 with h3|h3 <;> omega

theorem choose_none_without_overlap (t : RMAF.Tree) (A B : List Nat)
    (hno : ∀v,v∈RMAF.minimalVertices A t→v∈RMAF.minimalVertices B t→False) :
    choose t A B=none := by
  cases ho : choose t A B with
  | none => rfl
  | some o =>
    have hv := (choose_sound t A B o ho).2
    cases o with
    | vertex v => exact False.elim (hno v hv.1 hv.2.1)
    | edge e => exact False.elim (hno e.1 hv.2.1 hv.2.2.1)
end PairGeometry
