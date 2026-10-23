import ForestColorWork

namespace Universal233.WholeSourceWork
open RMAF VertexGeometry CoreProgram CoreWork WholeSourceMass

/-- Literal finite target span construction, including original unary addresses. -/
def meterRooted (D : List Nat) : Tree → Charged (List RMAF.Vertex)
  | .leaf x =>
    let m := meterContains x D
    ⟨if m.value then [[]] else [],m.work+8⟩
  | .node l r =>
    let a := meterRooted D l
    let b := meterRooted D r
    ⟨if a.value.isEmpty && b.value.isEmpty then [] else
      []::(prependSide false a.value ++ prependSide true b.value),
      a.work+b.work+8*(a.value.length+b.value.length+2)⟩

@[simp] theorem meterRooted_value (D T) :
    (meterRooted D T).value = rootedSpan D T := by
  induction T with
  | leaf x => simp [meterRooted,rootedSpan]
  | node l r ihl ihr => simp [meterRooted,rootedSpan,ihl,ihr]

theorem rooted_length (D : List Nat) (T : Tree) :
    (rootedSpan D T).length ≤ treeNodes T := by
  induction T with
  | leaf x => simp only [rootedSpan,treeNodes]; split <;> simp
  | node l r ihl ihr =>
    simp only [rootedSpan,treeNodes]
    split <;> simp only [List.length_nil,List.length_cons,prependSide,List.length_append,List.length_map] <;> omega

theorem meterRooted_bound (D : List Nat) (T : Tree) (M : Nat)
    (hM : treeNodes T ≤ M) :
    (meterRooted D T).work ≤ 16*(D.length+M+2)*treeNodes T := by
  induction T with
  | leaf x =>
    have hm := meterContains_bound x D
    simp only [meterRooted,treeNodes,Nat.mul_one]
    omega
  | node l r ihl ihr =>
    have hsum : treeNodes l+treeNodes r ≤ M := by simp only [treeNodes] at hM; omega
    have hl : treeNodes l ≤ M := by simp only [treeNodes] at hM; omega
    have hr : treeNodes r ≤ M := by simp only [treeNodes] at hM; omega
    have hwl := ihl hl
    have hwr := ihr hr
    have hll := rooted_length D l
    have hlr := rooted_length D r
    let K := 16*(D.length+M+2)
    change (meterRooted D l).work ≤ K*treeNodes l at hwl
    change (meterRooted D r).work ≤ K*treeNodes r at hwr
    have hk : 8*((rootedSpan D l).length+(rootedSpan D r).length+2) ≤ K := by
      dsimp [K]
      simp only [treeNodes] at hM
      omega
    change (meterRooted D l).work+(meterRooted D r).work+
      8*((meterRooted D l).value.length+(meterRooted D r).value.length+2) ≤
      K*(1+treeNodes l+treeNodes r)
    rw [meterRooted_value,meterRooted_value]
    calc
      _ ≤ K*treeNodes l+K*treeNodes r+K := by omega
      _ = _ := by simp only [Nat.mul_add,Nat.mul_one]; omega

def meterMinimal (D : List Nat) : Tree → Charged (List RMAF.Vertex)
  | .leaf x =>
    let m := meterContains x D
    ⟨if m.value then [[]] else [],m.work+8⟩
  | .node l r =>
    let a := meterRooted D l
    let b := meterRooted D r
    if a.value.isEmpty then
      let m := meterMinimal D r
      ⟨prependSide true m.value,a.work+b.work+m.work+8*(m.value.length+2)⟩
    else if b.value.isEmpty then
      let m := meterMinimal D l
      ⟨prependSide false m.value,a.work+b.work+m.work+8*(m.value.length+2)⟩
    else
      ⟨[]::(prependSide false a.value++prependSide true b.value),
        a.work+b.work+8*(a.value.length+b.value.length+2)⟩

@[simp] theorem meterMinimal_value (D T) :
    (meterMinimal D T).value = minimalVertices D T := by
  induction T with
  | leaf x => simp [meterMinimal,minimalVertices]
  | node l r ihl ihr =>
    simp only [meterMinimal,meterRooted_value,minimalVertices]
    split <;> simp_all
    split <;> simp_all

theorem minimal_length (D : List Nat) (T : Tree) :
    (minimalVertices D T).length ≤ treeNodes T := by
  induction T with
  | leaf x => simp only [minimalVertices,treeNodes]; split <;> simp
  | node l r ihl ihr =>
    have hl := rooted_length D l
    have hr := rooted_length D r
    simp only [minimalVertices,treeNodes]
    split
    · simp only [prependSide,List.length_map]; omega
    · split <;> simp only [List.length_cons,prependSide,List.length_append,List.length_map] <;> omega

def spanCap (D : List Nat) (M : Nat) : Nat := (16*(D.length+M+2)+16)*(M+1)

theorem meterMinimal_bound (D : List Nat) (T : Tree) (M : Nat)
    (hM : treeNodes T ≤ M) :
    (meterMinimal D T).work ≤ spanCap D M*treeNodes T := by
  induction T with
  | leaf x =>
    have hm := meterContains_bound x D
    have hp : 1 ≤ M+1 := by omega
    have he := Nat.mul_le_mul_left (16*(D.length+M+2)+16) hp
    simp only [Nat.mul_one] at he
    simp only [meterMinimal,treeNodes,Nat.mul_one,spanCap]
    omega
  | node l r ihl ihr =>
    have hsum : treeNodes l+treeNodes r ≤ M := by simp only [treeNodes] at hM; omega
    have hl : treeNodes l ≤ M := by simp only [treeNodes] at hM; omega
    have hr : treeNodes r ≤ M := by simp only [treeNodes] at hM; omega
    have hwl := ihl hl
    have hwr := ihr hr
    have hrl := meterRooted_bound D l M hl
    have hrr := meterRooted_bound D r M hr
    have hll := rooted_length D l
    have hlr := rooted_length D r
    have hml := minimal_length D l
    have hmr := minimal_length D r
    let K := 16*(D.length+M+2)
    have hrs : (meterRooted D l).work+(meterRooted D r).work ≤ K*M := by
      calc
        _ ≤ K*treeNodes l+K*treeNodes r := Nat.add_le_add hrl hrr
        _ = K*(treeNodes l+treeNodes r) := (Nat.mul_add _ _ _).symm
        _ ≤ K*M := Nat.mul_le_mul_left K (by simp only [treeNodes] at hM; omega)
    have hlocal : K*M+8*(M+2) ≤ spanCap D M := by
      change K*M+8*(M+2) ≤ (K+16)*(M+1)
      simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]
      omega
    have hout : spanCap D M*(1+treeNodes l+treeNodes r) =
      spanCap D M+spanCap D M*treeNodes l+spanCap D M*treeNodes r := by
      simp only [Nat.mul_add,Nat.mul_one]
    simp only [meterMinimal,meterRooted_value,treeNodes]
    split
    · simp only [meterMinimal_value]
      rw [hout]
      omega
    · split
      · simp only [meterMinimal_value]
        rw [hout]
        omega
      · rw [hout]
        dsimp only
        omega

/-- The actual Lean 4.35 eraseDupsBy loop: scan the accumulated list,
keep the first occurrence, then materialize its reverse. -/
def meterAnyEq {α : Type} [BEq α] (a : α) : List α → Charged Bool
  | [] => ⟨false,1⟩
  | b::bs => if a == b then ⟨true,4⟩ else
      let r := meterAnyEq a bs
      ⟨r.value,4+r.work⟩

@[simp] theorem meterAnyEq_value {α : Type} [BEq α] (a : α) (L : List α) :
    (meterAnyEq a L).value = L.any (a == ·) := by
  induction L with
  | nil => rfl
  | cons b bs ih => cases h : a == b <;> simp [meterAnyEq,List.any_cons,h,ih]

theorem meterAnyEq_bound {α : Type} [BEq α] (a : α) (L : List α) :
    (meterAnyEq a L).work ≤ 4*(L.length+1) := by
  induction L with
  | nil => simp [meterAnyEq]
  | cons b bs ih =>
    simp only [meterAnyEq,List.length_cons]
    split <;> (try simp only [Charged.work]) <;> omega

def meterDupsLoop {α : Type} [BEq α] : List α → List α → Charged (List α)
  | [], acc => ⟨acc.reverse,4*(acc.length+1)⟩
  | a::as, acc =>
    let h := meterAnyEq a acc
    let r := if h.value then meterDupsLoop as acc else meterDupsLoop as (a::acc)
    ⟨r.value,h.work+r.work+4⟩

@[simp] theorem meterDupsLoop_value {α : Type} [BEq α] (L acc : List α) :
    (meterDupsLoop L acc).value = List.eraseDupsBy.loop (· == ·) L acc := by
  induction L generalizing acc with
  | nil => rfl
  | cons a as ih =>
    simp only [meterDupsLoop,meterAnyEq_value,List.eraseDupsBy.loop]
    cases h : acc.any (a == ·) <;> simp [h,ih]

theorem meterDupsLoop_bound {α : Type} [BEq α] (L acc : List α) (M : Nat)
    (hM : L.length+acc.length ≤ M) :
    (meterDupsLoop L acc).work ≤ 8*(M+1)*(L.length+1) := by
  induction L generalizing acc with
  | nil => simp only [meterDupsLoop,List.length_nil,Nat.zero_add,Nat.mul_one] at *; omega
  | cons a as ih =>
    have hm := meterAnyEq_bound a acc
    have h1 : as.length+acc.length ≤ M := by simp only [List.length_cons] at hM; omega
    have h2 : as.length+(a::acc).length ≤ M := by simp only [List.length_cons] at *; omega
    have ha := ih acc h1
    have hb := ih (a::acc) h2
    have hc : 4*(acc.length+1)+4 ≤ 8*(M+1) := by simp only [List.length_cons] at hM; omega
    have he : 8*(M+1)*((a::as).length+1) = 8*(M+1)+8*(M+1)*(as.length+1) := by
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]; omega
    rw [he]
    simp only [meterDupsLoop]
    split <;> (try simp only [Charged.work]) <;> omega

def meterDups {α : Type} [BEq α] (L : List α) : Charged (List α) := meterDupsLoop L []

@[simp] theorem meterDups_value {α : Type} [BEq α] (L : List α) :
    (meterDups L).value = L.eraseDups := by
  simp [meterDups,List.eraseDups,List.eraseDupsBy]

theorem meterDups_bound {α : Type} [BEq α] (L : List α) (M : Nat) (hM : L.length ≤ M) :
    (meterDups L).work ≤ 8*(M+1)*(L.length+1) := by
  exact meterDupsLoop_bound L [] M (by simpa using hM)

def meterJointMap (v w : RMAF.Vertex) : List RMAF.Vertex → Charged (List (Nat×Nat))
  | [] => ⟨[],1⟩
  | a::as =>
    let p := meterRegion v a
    let q := meterRegion w a
    let r := meterJointMap v w as
    ⟨(p.value,q.value)::r.value,p.work+q.work+r.work+6⟩

@[simp] theorem meterJointMap_value (v w L) :
    (meterJointMap v w L).value = L.map (jointRegion v w) := by
  induction L with
  | nil => rfl
  | cons a as ih => simp [meterJointMap,jointRegion,ih]

def jointMapCap (v w : RMAF.Vertex) : Nat := 4*(v.length+1)+4*(w.length+1)+6

theorem meterJointMap_bound (v w L) :
    (meterJointMap v w L).work ≤ jointMapCap v w*L.length+1 := by
  induction L with
  | nil => simp [meterJointMap]
  | cons a as ih =>
    have hp := meterRegion_bound v a
    have hq := meterRegion_bound w a
    simp only [meterJointMap,List.length_cons,Nat.mul_add,Nat.mul_one]
    unfold jointMapCap at *
    omega

def meterJointColors (D : List Nat) (T : Tree) (v w : RMAF.Vertex) : Charged (List (Nat×Nat)) :=
  let a := meterLeafList D T
  let b := meterJointMap v w a.value
  let c := meterDups b.value
  ⟨c.value,a.work+b.work+c.work+4⟩

@[simp] theorem meterJointColors_value (D T v w) :
    (meterJointColors D T v w).value = jointColors D T v w := by
  simp [meterJointColors,jointColors]

def jointGateCap (D : List Nat) (T : Tree) (v w : RMAF.Vertex) : Nat :=
  16*(D.length+treeNodes T+2)*treeNodes T+
    jointMapCap v w*treeNodes T+8*(treeNodes T+1)*(treeNodes T+1)+5

theorem meterJointColors_bound (D T v w) :
    (meterJointColors D T v w).work ≤ jointGateCap D T v w := by
  have ha := meterLeafList_bound D T (treeNodes T) (Nat.le_refl _)
  have hb := meterJointMap_bound v w (leafList D T)
  have hl := leafList_length D T
  have hc := meterDups_bound ((leafList D T).map (jointRegion v w)) (treeNodes T)
    (by simpa using hl)
  have hm := Nat.mul_le_mul_left (jointMapCap v w) hl
  have hd := Nat.mul_le_mul_left (8*(treeNodes T+1)) (Nat.add_le_add_right hl 1)
  simp only [List.length_map] at hc
  simp only [meterJointColors,meterLeafList_value,meterJointMap_value,jointGateCap]
  omega

theorem leaves_pos (T : Tree) : 1 ≤ (leaves T).length := by
  have h := treeNodes_le_twice_leaves T
  have hp := treeNodes_pos T
  omega

theorem rooted_address (D : List Nat) (T : Tree) (v : RMAF.Vertex)
    (hv : v ∈ rootedSpan D T) : v.length < (leaves T).length := by
  induction T generalizing v with
  | leaf x =>
    simp only [rootedSpan] at hv
    split at hv <;> simp_all [leaves]
  | node l r ihl ihr =>
    have hp := leaves_pos l
    have hq := leaves_pos r
    simp only [rootedSpan] at hv
    split at hv
    · simp at hv
    · simp only [List.mem_cons,List.mem_append] at hv
      rcases hv with hv | hv | hv
      · subst v; simp only [List.length_nil,leaves,List.length_append]; omega
      · obtain ⟨a,ha,he⟩ := List.mem_map.mp hv
        subst v
        have hh := ihl a ha
        simp only [List.length_cons,leaves,List.length_append]; omega
      · obtain ⟨a,ha,he⟩ := List.mem_map.mp hv
        subst v
        have hh := ihr a ha
        simp only [List.length_cons,leaves,List.length_append]; omega

theorem minimal_address (D : List Nat) (T : Tree) (v : RMAF.Vertex)
    (hv : v ∈ minimalVertices D T) : v.length < (leaves T).length := by
  induction T generalizing v with
  | leaf x =>
    simp only [minimalVertices] at hv
    split at hv <;> simp_all [leaves]
  | node l r ihl ihr =>
    have hp := leaves_pos l
    have hq := leaves_pos r
    simp only [minimalVertices] at hv
    split at hv
    · obtain ⟨a,ha,he⟩ := List.mem_map.mp hv
      subst v
      have hh := ihr a ha
      simp only [List.length_cons,leaves,List.length_append]; omega
    · split at hv
      · obtain ⟨a,ha,he⟩ := List.mem_map.mp hv
        subst v
        have hh := ihl a ha
        simp only [List.length_cons,leaves,List.length_append]; omega
      · simp only [List.mem_cons,List.mem_append] at hv
        rcases hv with hv | hv | hv
        · subst v; simp only [List.length_nil,leaves,List.length_append]; omega
        · obtain ⟨a,ha,he⟩ := List.mem_map.mp hv
          subst v
          have hh := rooted_address D l a ha
          simp only [List.length_cons,leaves,List.length_append]; omega
        · obtain ⟨a,ha,he⟩ := List.mem_map.mp hv
          subst v
          have hh := rooted_address D r a ha
          simp only [List.length_cons,leaves,List.length_append]; omega

def meterAddressEq : RMAF.Vertex → RMAF.Vertex → Charged Bool
  | [], [] => ⟨true,2⟩
  | [], _::_ => ⟨false,2⟩
  | _::_, [] => ⟨false,2⟩
  | a::as,b::bs => if a == b then
      let r := meterAddressEq as bs
      ⟨r.value,4+r.work⟩ else ⟨false,4⟩

@[simp] theorem meterAddressEq_value (v w : RMAF.Vertex) :
    (meterAddressEq v w).value = (v == w) := by
  induction v generalizing w with
  | nil => cases w <;> rfl
  | cons a as ih =>
    cases w with
    | nil => rfl
    | cons b bs => cases h : a == b <;> simp [meterAddressEq,h,ih]

theorem meterAddressEq_bound (v w : RMAF.Vertex) :
    (meterAddressEq v w).work ≤ 4*(v.length+1) := by
  induction v generalizing w with
  | nil => cases w <;> simp [meterAddressEq]
  | cons a as ih =>
    cases w with
    | nil => simp only [meterAddressEq,List.length_cons]; omega
    | cons b bs =>
      have h := ih bs
      simp only [meterAddressEq,List.length_cons]
      split <;> (try simp only [Charged.work]) <;> omega

def meterVertexContains (v : RMAF.Vertex) : List RMAF.Vertex → Charged Bool
  | [] => ⟨false,1⟩
  | w::ws =>
    let h := meterAddressEq v w
    if h.value then ⟨true,h.work+4⟩ else
      let r := meterVertexContains v ws
      ⟨r.value,h.work+r.work+4⟩

@[simp] theorem meterVertexContains_value (v L) :
    (meterVertexContains v L).value = L.contains v := by
  induction L with
  | nil => rfl
  | cons w ws ih =>
    simp only [meterVertexContains,meterAddressEq_value,List.contains_cons]
    cases h : v == w <;> simp [h,ih]

theorem meterVertexContains_bound (v L M) (hv : v.length ≤ M) :
    (meterVertexContains v L).work ≤ 8*(M+1)*(L.length+1) := by
  induction L with
  | nil => simp only [meterVertexContains,List.length_nil,Nat.zero_add,Nat.mul_one]; omega
  | cons w ws ih =>
    have hh := meterAddressEq_bound v w
    have hc : 4*(v.length+1)+4 ≤ 8*(M+1) := by omega
    have he : 8*(M+1)*((w::ws).length+1) = 8*(M+1)+8*(M+1)*(ws.length+1) := by
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]; omega
    rw [he]
    simp only [meterVertexContains]
    split <;> (try simp only [Charged.work]) <;> omega

def meterCommon (A B C : List RMAF.Vertex) : Charged (Option RMAF.Vertex) :=
  match A with
  | [] => ⟨none,1⟩
  | v::vs =>
    let b := meterVertexContains v B
    let c := meterVertexContains v C
    if b.value && c.value then ⟨some v,b.work+c.work+6⟩ else
      let r := meterCommon vs B C
      ⟨r.value,b.work+c.work+r.work+6⟩

@[simp] theorem meterCommon_value (A B C) :
    (meterCommon A B C).value = findCommon A B C := by
  induction A with
  | nil => rfl
  | cons v vs ih =>
    simp only [meterCommon,meterVertexContains_value,findCommon]
    split <;> simp_all

def commonCap (M : Nat) := 32*((M+1)*(M+1))

theorem meterCommon_bound (A B C : List RMAF.Vertex) (M : Nat)
    (hA : ∀ v, v ∈ A → v.length ≤ M) (hB : B.length ≤ M) (hC : C.length ≤ M) :
    (meterCommon A B C).work ≤ commonCap M*(A.length+1) := by
  have hp0 : 1 ≤ (M+1)*(M+1) := by
    have h := Nat.mul_le_mul (show 1 ≤ M+1 by omega) (show 1 ≤ M+1 by omega)
    simpa using h
  induction A with
  | nil => simp only [meterCommon,List.length_nil,Nat.zero_add,Nat.mul_one,commonCap]; omega
  | cons v vs ih =>
    have hv := hA v (by simp)
    have hi := ih (by intro w hw; exact hA w (by simp [hw]))
    have hb := meterVertexContains_bound v B M hv
    have hc := meterVertexContains_bound v C M hv
    have hbb := Nat.mul_le_mul_left (8*(M+1)) (Nat.add_le_add_right hB 1)
    have hcc := Nat.mul_le_mul_left (8*(M+1)) (Nat.add_le_add_right hC 1)
    have hl : (meterVertexContains v B).work+(meterVertexContains v C).work+6 ≤ commonCap M := by
      unfold commonCap
      simp only [Nat.mul_assoc] at hb hc hbb hcc
      omega
    have he : commonCap M*((v::vs).length+1) = commonCap M+commonCap M*(vs.length+1) := by
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]; omega
    rw [he]
    simp only [meterCommon]
    split <;> (try simp only [Charged.work]) <;> omega

/-- Only the frozen clique/common-vertex selector is included. Pair G/E
selectors and all hard-parent/refinement history are excluded. -/
def meterCliqueSelection (T : Tree) (A B C : List Nat) : Charged (Option RMAF.Vertex) :=
  let a := meterMinimal A T
  let b := meterMinimal B T
  let c := meterMinimal C T
  let r := meterCommon a.value b.value c.value
  ⟨r.value,a.work+b.work+c.work+r.work+4⟩

@[simp] theorem meterCliqueSelection_value (T A B C) :
    (meterCliqueSelection T A B C).value =
      findCommon (minimalVertices A T) (minimalVertices B T) (minimalVertices C T) := by
  simp [meterCliqueSelection]

def selectionCap (T : Tree) (A B C : List Nat) : Nat :=
  (spanCap A (treeNodes T)+spanCap B (treeNodes T)+spanCap C (treeNodes T))*treeNodes T+
    commonCap (treeNodes T)*(treeNodes T+1)+4

theorem meterCliqueSelection_bound (T A B C) :
    (meterCliqueSelection T A B C).work ≤ selectionCap T A B C := by
  have ha := meterMinimal_bound A T (treeNodes T) (Nat.le_refl _)
  have hb := meterMinimal_bound B T (treeNodes T) (Nat.le_refl _)
  have hc := meterMinimal_bound C T (treeNodes T) (Nat.le_refl _)
  have hlen := minimal_length A T
  have hcomm := meterCommon_bound (minimalVertices A T) (minimalVertices B T) (minimalVertices C T)
    (treeNodes T) (by
      intro v hv
      have h := minimal_address A T v hv
      have hn := treeNodes_le_twice_leaves T
      have hp := treeNodes_pos T
      omega) (minimal_length B T) (minimal_length C T)
  have hmul := Nat.mul_le_mul_left (commonCap (treeNodes T)) (Nat.add_le_add_right hlen 1)
  simp only [meterCliqueSelection,meterMinimal_value,selectionCap,Nat.add_mul]
  omega

end Universal233.WholeSourceWork
