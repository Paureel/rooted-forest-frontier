import RCGroups
namespace OrdinaryDispatch.RecoveryControlBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits

theorem word_test_fee (W N : Nat) (x y : List Bool) (xw : x.length≤W) (yw : y.length≤W) :
 (ownedEqual x y).work+8≤2*groupFee W N := by
 have a:=ownedEqual_work W x y xw yw
 have b:64*(W+4)≤groupFee W N:=by
  simpa only [groupFee,Nat.mul_one] using Nat.mul_le_mul_left (64*(W+4)) (show 1≤N+1 by omega)
 omega

def allColor (color : List Bool) : List BitGroup→Charged Bool
 | []=>⟨true,2⟩
 | g::gs=>let a:=ownedEqual g.color color;let r:=allColor color gs
   ⟨a.value&&r.value,a.work+r.work+4⟩
@[simp] theorem allColor_value (color : List Bool) (gs : List BitGroup) :
 (allColor color gs).value=(gs.map viewGroup).all (fun g=>g.color==decode color) := by
 induction gs <;> simp_all [allColor,viewGroup]
theorem allColor_work (W N : Nat) (color : List Bool) (gs : List BitGroup)
 (cw : color.length≤W) (caps : GroupCaps W N gs) :
 (allColor color gs).work≤3*groupFee W N*(gs.length+1) := by
 have pos:=groupFee_positive W N
 induction gs with
 | nil=>simp only [allColor,List.length_nil,Nat.zero_add,Nat.mul_one];omega
 | cons g gs ih=>
  have a:=word_test_fee W N g.color color (caps g (by simp)).2.1 cw
  have b:=ih (by intro x hx;exact caps x (by simp [hx]))
  simp only [allColor,List.length_cons,Nat.mul_add,Nat.mul_one] at b ⊢
  omega

def filterColor (color : List Bool) : List BitGroup→Charged (List BitGroup)
 | []=>⟨[],2⟩
 | g::gs=>let e:=ownedEqual g.color color;let tail:=filterColor color gs
   if e.value then let c:=copyGroup g;⟨c.value::tail.value,e.work+tail.work+c.work+8⟩
   else ⟨tail.value,e.work+tail.work+8⟩
@[simp] theorem filterColor_value (color : List Bool) (gs : List BitGroup) :
 (filterColor color gs).value=gs.filter (fun g=>decode g.color==decode color) := by
 induction gs with
 | nil=>rfl
 | cons g gs ih=>simp [filterColor,ih];split <;> simp_all
@[simp] theorem filterColor_view (color : List Bool) (gs : List BitGroup) :
 ((filterColor color gs).value.map viewGroup)=(gs.map viewGroup).filter (fun g=>g.color==decode color) := by
 induction gs with
 | nil=>rfl
 | cons g gs ih=>
  simp only [filterColor,List.map_cons,List.filter_cons,viewGroup,ownedEqual_value]
  split <;> simp_all

theorem filterColor_length (color : List Bool) (gs : List BitGroup) :
 (filterColor color gs).value.length≤gs.length := by
 rw [filterColor_value];exact List.length_filter_le _ _

theorem filterColor_caps (W N : Nat) (color : List Bool) (gs : List BitGroup) (h : GroupCaps W N gs) :
 GroupCaps W N (filterColor color gs).value := by
 rw [filterColor_value];intro g hg;exact h g (List.mem_filter.mp hg).1

theorem filterColor_work (W N : Nat) (color : List Bool) (gs : List BitGroup)
 (cw : color.length≤W) (caps : GroupCaps W N gs) :
 (filterColor color gs).work≤4*groupFee W N*(gs.length+1) := by
 have pos:=groupFee_positive W N
 induction gs with
 | nil=>simp only [filterColor,List.length_nil,Nat.zero_add,Nat.mul_one];omega
 | cons g gs ih=>
  have e:=word_test_fee W N g.color color (caps g (by simp)).2.1 cw
  have c:=copied_group_fee W N g (caps g (by simp))
  have r:=ih (by intro x hx;exact caps x (by simp [hx]))
  simp only [filterColor,List.length_cons,Nat.mul_add,Nat.mul_one] at r ⊢
  split <;> simp only [Charged.work] <;> omega

def uniqueTest (W : Nat) (gs : List BitGroup) (g : BitGroup) : Charged Bool :=
 let f:=filterColor g.color gs;let n:=lengthOwned W f.value
 let e:=ownedEqual n.value [true];let cf:=closeGroups f.value;let cn:=closeBits n.value
 ⟨e.value,f.work+n.work+e.work+cf.work+cn.work+12⟩

@[simp] theorem uniqueTest_value (W : Nat) (gs : List BitGroup) (g : BitGroup)
 (fits : gs.length<2^W) :
 (uniqueTest W gs g).value=(((gs.map viewGroup).filter (fun h=>h.color==(viewGroup g).color)).length==1) := by
 have len: (filterColor g.color gs).value.length<2^W:=Nat.lt_of_le_of_lt (filterColor_length _ _) fits
 have eq:(filterColor g.color gs).value.length=((gs.map viewGroup).filter (fun h=>h.color==decode g.color)).length:=by
  rw [←filterColor_view,List.length_map]
 simp only [uniqueTest,ownedEqual_value,lengthOwned_value W _ len,decode,bit,ite_true,Nat.mul_zero,Nat.add_zero,eq,viewGroup]

theorem uniqueTest_work (W N : Nat) (gs : List BitGroup) (g : BitGroup)
 (positive : 1≤W) (caps : GroupCaps W N gs) (gc : GroupCap W N g) (size : gs.length≤N) :
 (uniqueTest W gs g).work≤16*groupFee W N*(N+1) := by
 let G:=groupFee W N;let K:=G*(N+1)
 have pos:=groupFee_positive W N
 have flen:=filterColor_length g.color gs
 have fcap:=filterColor_caps W N g.color gs caps
 have f:=filterColor_work W N g.color gs gc.2.1 caps
 have l:=lengthOwned_work W (filterColor g.color gs).value
 have lw:=lengthOwned_length W (filterColor g.color gs).value
 have e:=word_test_fee W N (lengthOwned W (filterColor g.color gs).value).value [true] lw (by simpa)
 have c:=closeGroups_work W N (filterColor g.color gs).value fcap
 have widen:72*(W+1)≤2*G:=by
  have a:64*(W+4)≤G:=by simpa only [G,groupFee,Nat.mul_one] using Nat.mul_le_mul_left (64*(W+4)) (show 1≤N+1 by omega)
  omega
 have fmax:=Nat.mul_le_mul_left (4*G) (Nat.add_le_add_right size 1)
 have lmax:=Nat.mul_le_mul widen (Nat.add_le_add_right (Nat.le_trans flen size) 1)
 have cmax:=Nat.mul_le_mul_left G (Nat.add_le_add_right (Nat.le_trans flen size) 1)
 have gk:G≤K:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left G (show 1≤N+1 by omega)
 have word:4*W+1≤G:=by
  have a:64*(W+4)≤G:=by simpa only [G,groupFee,Nat.mul_one] using Nat.mul_le_mul_left (64*(W+4)) (show 1≤N+1 by omega)
  omega
 change (filterColor g.color gs).work≤4*G*(gs.length+1) at f
 have fk:(filterColor g.color gs).work≤4*K:=by simpa only [K,Nat.mul_assoc] using Nat.le_trans f fmax
 have lk:(lengthOwned W (filterColor g.color gs).value).work≤2*K:=by simpa only [K,Nat.mul_assoc] using Nat.le_trans l lmax
 have ck:(closeGroups (filterColor g.color gs).value).work≤K:=Nat.le_trans c cmax
 dsimp only [G] at *
 simp only [uniqueTest,closeBits_work]
 calc _≤16*K:=by omega
      _=16*groupFee W N*(N+1):=by simp only [K,G,Nat.mul_assoc]

def findUnique (W : Nat) (whole : List BitGroup) : List BitGroup→Charged (Option BitGroup)
 | []=>⟨none,2⟩
 | g::gs=>let u:=uniqueTest W whole g
   if u.value then let c:=copyGroup g;⟨some c.value,u.work+c.work+8⟩
   else let r:=findUnique W whole gs;⟨r.value,u.work+r.work+8⟩

@[simp] theorem findUnique_value (W : Nat) (whole candidates : List BitGroup) (fits : whole.length<2^W) :
 (findUnique W whole candidates).value.map viewGroup=
 (candidates.map viewGroup).find? (fun g=>((whole.map viewGroup).filter (fun h=>h.color==g.color)).length==1) := by
 induction candidates with
 | nil=>rfl
 | cons g gs ih=>
  cases hc:(((whole.map viewGroup).filter (fun h=>h.color==(viewGroup g).color)).length==1) <;>
   simp [findUnique,uniqueTest_value W whole g fits,List.find?_cons,hc,ih]

theorem findUnique_mem (W : Nat) (whole candidates : List BitGroup) (g : BitGroup)
 (h : (findUnique W whole candidates).value=some g) : g∈candidates := by
 induction candidates with
 | nil=>simp [findUnique] at h
 | cons x xs ih=>
  simp only [findUnique] at h
  split at h
  · simp only [copyGroup_value,Option.some.injEq] at h;subst g;simp
  · exact List.mem_cons_of_mem _ (ih h)

theorem findUnique_work (W N : Nat) (whole candidates : List BitGroup)
 (positive : 1≤W) (wc : GroupCaps W N whole) (cc : GroupCaps W N candidates) (size : whole.length≤N) :
 (findUnique W whole candidates).work≤20*groupFee W N*(N+1)*(candidates.length+1) := by
 let K:=groupFee W N*(N+1)
 have gk:groupFee W N≤K:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (groupFee W N) (show 1≤N+1 by omega)
 have pos:64≤K:=Nat.le_trans (groupFee_positive W N) gk
 have aux (xs : List BitGroup) (caps : GroupCaps W N xs) :
  (findUnique W whole xs).work≤20*K*(xs.length+1):=by
  induction xs with
  | nil=>simp only [findUnique,List.length_nil,Nat.zero_add,Nat.mul_one];omega
  | cons g gs ih=>
   have u:(uniqueTest W whole g).work≤16*K:=by
    simpa only [K,Nat.mul_assoc] using uniqueTest_work W N whole g positive wc (caps g (by simp)) size
   have c:=copied_group_fee W N g (caps g (by simp))
   have r:=ih (by intro x hx;exact caps x (by simp [hx]))
   simp only [findUnique,List.length_cons,Nat.mul_add,Nat.mul_one] at r ⊢
   split <;> simp only [Charged.work] <;> omega
 simpa only [K,Nat.mul_assoc] using aux candidates cc

end OrdinaryDispatch.RecoveryControlBits
