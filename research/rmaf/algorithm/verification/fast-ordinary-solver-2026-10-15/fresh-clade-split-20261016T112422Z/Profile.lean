import Controls
namespace FreshClade
open RMAF

structure Profile where
  c : Bool
  d : Bool
  ms : Bool
  sm : Bool
  mm : Bool
deriving DecidableEq

def zero : Profile := ⟨false,false,false,false,false⟩
def merge (a b : Profile) : Profile :=
 ⟨a.c || b.c, a.d || b.d,
  (a.c && b.c && (a.d || b.d)) || (!b.c && a.ms) || (!a.c && b.ms),
  (a.d && b.d && (a.c || b.c)) || (!b.d && a.sm) || (!a.d && b.sm),
  (a.c && b.c && a.d && b.d) ||
  (a.c && b.c && !b.d && a.sm) || (a.c && b.c && !a.d && b.sm) ||
  (a.d && b.d && !b.c && a.ms) || (a.d && b.d && !a.c && b.ms) ||
  (!b.c && !b.d && a.mm) || (!a.c && !a.d && b.mm)⟩

def profile (C D : List Nat) : Tree → Profile
 | .leaf x => let c := C.contains x; let d := D.contains x; ⟨c,d,c&&d,c&&d,c&&d⟩
 | .node l r => merge (profile C D l) (profile C D r)

theorem merge_zero (a : Profile) : merge a zero = a ∧ merge zero a = a := by
 cases a
 simp [merge,zero]

theorem merge_comm (a b : Profile) : merge a b = merge b a := by
 cases a with | mk ac ad ams asm amm =>
  cases b with | mk bc bd bms bsm bmm =>
   cases ac <;> cases ad <;> cases bc <;> cases bd <;>
    simp [merge, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]

def optProfile (C D : List Nat) : Option Tree → Profile
 | none => zero
 | some T => profile C D T

theorem profile_restrict (B C D : List Nat)
 (hC : ∀ x, x ∈ C → x ∈ B) (hD : ∀ x, x ∈ D → x ∈ B) (T : Tree) :
 optProfile C D (restrict B T) = profile C D T := by
 induction T with
 | leaf x =>
   by_cases hb : x ∈ B
   · simp [restrict,profile,optProfile,hb]
   · have hc : x ∉ C := fun h => hb (hC x h)
     have hd : x ∉ D := fun h => hb (hD x h)
     simp [restrict,profile,optProfile,zero,hb,hc,hd]
 | node l r il ir =>
   cases hl : restrict B l with
   | none =>
     cases hr : restrict B r with
     | none =>
       simp [hl,optProfile] at il
       simp [hr,optProfile] at ir
       simp [restrict,hl,hr,optProfile,profile,←il,←ir,merge_zero]
     | some R =>
       simp [hl,optProfile] at il
       simp [hr,optProfile] at ir
       simp [restrict,hl,hr,optProfile,profile,←il,←ir,merge_zero]
   | some L =>
     cases hr : restrict B r with
     | none =>
       simp [hl,optProfile] at il
       simp [hr,optProfile] at ir
       simp [restrict,hl,hr,optProfile,profile,←il,←ir,merge_zero]
     | some R =>
       simp [hl,optProfile] at il
       simp [hr,optProfile] at ir
       simp [restrict,hl,hr,optProfile,profile,←il,←ir]

theorem profile_iso (C D : List Nat) {T S : Tree} (h : RootedIso T S) :
 profile C D T = profile C D S := by
 induction h with
 | leaf x => rfl
 | straight h₁ h₂ i₁ i₂ => simp [profile,i₁,i₂]
 | swapped h₁ h₂ i₁ i₂ => simp [profile,i₁,i₂,merge_comm]

theorem sameShape_iso {T S : Tree} (h : sameShape T S = true) : RootedIso T S := by
 induction T generalizing S with
 | leaf x =>
   cases S with
   | leaf y => simp [sameShape] at h; subst y; exact .leaf x
   | node l r => simp [sameShape] at h
 | node l r il ir =>
   cases S with
   | leaf x => simp [sameShape] at h
   | node a b =>
     simp only [sameShape,Bool.or_eq_true,Bool.and_eq_true] at h
     rcases h with h|h
     · exact .straight (il h.1) (ir h.2)
     · exact .swapped (il h.1) (ir h.2)

theorem iso_sameShape {T S : Tree} (h : RootedIso T S) : sameShape T S = true := by
 induction h with
 | leaf x => simp [sameShape]
 | straight h₁ h₂ i₁ i₂ => simp [sameShape,i₁,i₂]
 | swapped h₁ h₂ i₁ i₂ => simp [sameShape,i₁,i₂]

theorem profile_transport (B C D : List Nat)
 (hC : ∀ x, x ∈ C → x ∈ B) (hD : ∀ x, x ∈ D → x ∈ B)
 {T S : Tree} (h : restrictionAgrees T S B = true) :
 profile C D T = profile C D S := by
 unfold restrictionAgrees at h
 cases ht : restrict B T with
 | none => simp [ht] at h
 | some t =>
   cases hs : restrict B S with
   | none => simp [ht,hs] at h
   | some s =>
     simp only [ht,hs] at h
     have e := profile_iso C D (sameShape_iso h)
     have et := profile_restrict B C D hC hD T
     have es := profile_restrict B C D hC hD S
     simp only [ht,optProfile] at et
     simp only [hs,optProfile] at es
     exact et.symm.trans (e.trans es)
end FreshClade
