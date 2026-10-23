import RWChoose
namespace OrdinaryDispatch.RecoveryLocalWork
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.OptimizerLocalWork

def meterAttempt (f : GTree→List Group→List RMAF.Vertex→Charged Receipt)
 (t : GTree) (d : List Group) (c : List RMAF.Vertex) (g : Group) : Charged Receipt :=
 let contains:=meterVertexContains g.origin c;let erased:=meterErase g.origin t
 let fee:=contains.work+erased.work+16
 if g.origin=[] then ⟨⟨[],["attempt to cut original root"],0,1,0⟩,fee⟩
 else if contains.value then ⟨⟨[],["duplicate original source cut"],0,1,0⟩,fee⟩
 else match erased.value with
 | none=>⟨⟨[],["attempt removed entire current source"],0,1,0⟩,fee⟩
 | some next=>let r:=f next (g::d) (g.origin::c)
   ⟨{r.value with childAttempts:=r.value.childAttempts+1},fee+r.work+8⟩
@[simp] theorem meterAttempt_value (f t d c g) :
 (meterAttempt f t d c g).value=CoreProgram.attempt (fun t d c=>(f t d c).value) t d c g := by
 simp only [meterAttempt,meterVertexContains_value,meterErase_value,CoreProgram.attempt]
 split <;> try rfl
 split <;> try rfl
 cases h:CoreProgram.erase g.origin t <;> rfl

theorem meterAttempt_bound (f : GTree→List Group→List RMAF.Vertex→Charged Receipt)
 (t : GTree) (d : List Group) (c : List RMAF.Vertex) (g : Group) (N B : Nat)
 (tn : footprint t≤N) (cn : c.length≤N) (gn : g.origin.length≤N)
 (callback : ∀next,CoreProgram.erase g.origin t=some next → (f next (g::d) (g.origin::c)).work≤B) :
 (meterAttempt f t d c g).work≤B+128*(N+1)^2 := by
 have mem:=meterVertexContains_bound g.origin c N gn
 have erase:=meterErase_bound g.origin t N tn
 have ms:=Nat.mul_le_mul_left (8*(N+1)) (Nat.add_le_add_right cn 1)
 have es:=Nat.mul_le_mul_left (32*(N+1)) (Nat.le_trans tn (Nat.le_succ N))
 have mcap : (meterVertexContains g.origin c).work≤8*(N+1)^2:=Nat.le_trans mem (by simpa only [Nat.pow_two,Nat.mul_assoc] using ms)
 have ecap : (meterErase g.origin t).work≤32*(N+1)^2:=Nat.le_trans erase (by simpa only [Nat.pow_two,Nat.mul_assoc] using es)
 have pos : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
 simp only [meterAttempt,meterVertexContains_value,meterErase_value]
 split
 · simp only [Charged.work];omega
 · split
   · simp only [Charged.work];omega
   · cases h:CoreProgram.erase g.origin t with
     | none=>simp only [h];omega
     | some next=>have r:=callback next h;simp only [h];omega

theorem meterAttempt_records (f : GTree→List Group→List RMAF.Vertex→Charged Receipt)
 (t : GTree) (d : List Group) (c : List RMAF.Vertex) (g : Group) (R : Nat) (pos : 1≤R)
 (callback : ∀t d c,records (f t d c).value≤R) :
 records (meterAttempt f t d c g).value≤R := by
 rw [meterAttempt_value]
 simp only [CoreProgram.attempt]
 split
 · simpa only [records,List.length_nil,List.length_cons] using pos
 · split
   · simpa only [records,List.length_nil,List.length_cons] using pos
   · cases h:CoreProgram.erase g.origin t with
     | none=>simpa only [h,records,List.length_nil,List.length_cons] using pos
     | some next=>simpa only [h,records] using callback next (g::d) (g.origin::c)

def meterOutput (t : GTree) (d : List Group) (c : List RMAF.Vertex) : Charged Output :=
 let ds:=meterMap (fun g:Group=>⟨g.labels,2⟩) d
 let gs:=meterGroups t
 let flat:=meterFlatMap (fun g:Group=>⟨g.labels,2⟩) gs.value
 ⟨⟨ds.value++[flat.value],c⟩,ds.work+gs.work+flat.work+4*(ds.value.length+1)+12⟩
@[simp] theorem meterOutput_value (t d c) :
 (meterOutput t d c).value=⟨d.map Group.labels++[(groups t).flatMap Group.labels],c⟩ := by simp [meterOutput]

theorem meterOutput_bound (t : GTree) (d : List Group) (c : List RMAF.Vertex) (N : Nat)
 (tn : footprint t≤N) (dn : d.length≤N) : (meterOutput t d c).work≤64*(N+1)^3 := by
 have groups:=meterGroups_bound t N tn
 have gs:=Nat.mul_le_mul_left (16*(N+1)) (Nat.le_trans tn (Nat.le_succ N))
 have glen:=Nat.le_trans (groups_length t) tn
 have map:=meterMap_bound (fun g:Group=>⟨g.labels,2⟩) d 2 (by intro _ _;exact Nat.le_refl _)
 have flat:=meterFlatMap_bound (fun g:Group=>⟨g.labels,2⟩) (CoreProgram.groups t) 2 N
  (by intro _ _;exact Nat.le_refl _) (by intro g hg;have z:=group_size t g hg;dsimp;omega)
 have scale:=Nat.mul_le_mul (show 2+6*(N+1)≤8*(N+1) by omega) (Nat.add_le_add_right glen 1)
 have fc : (meterFlatMap (fun g:Group=>⟨g.labels,2⟩) (CoreProgram.groups t)).work≤8*(N+1)^2:=
  Nat.le_trans flat (by simpa only [Nat.pow_two,Nat.mul_assoc] using scale)
 have gc : (meterGroups t).work≤16*(N+1)^2:=Nat.le_trans groups (by simpa only [Nat.pow_two,Nat.mul_assoc] using gs)
 have p1 : N+1≤(N+1)^3:=by simpa using pow_mono N 1 3 (by decide)
 have p2:=pow_mono N 2 3 (by decide)
 have pos : 1≤(N+1)^3:=Nat.one_le_pow _ _ (by omega)
 have f3:=cap_lift N 8 2 3 _ fc (by decide);have g3:=cap_lift N 16 2 3 _ gc (by decide)
 have mc:=Nat.le_trans map (Nat.mul_le_mul_left 6 (Nat.add_le_add_right dn 1))
 simp only [meterOutput,meterGroups_value,meterMap_value,List.length_map];omega

/-- Concrete source helper costs. The combined receipt append is charged by
both actual left-list lengths, even when they are exponential in the budget. -/
def meterStep (f : GTree→List Group→List RMAF.Vertex→Charged Receipt)
 (current : GTree) (d : List Group) (c : List RMAF.Vertex) : Charged Receipt :=
 let n:=meterNormalize current;let ch:=meterChoose n.value
 match ch.value with
 | .finish=>let o:=meterOutput n.value d c
   ⟨⟨[o.value],[],1,0,0⟩,n.work+ch.work+o.work+32⟩
 | .one g=>let a:=meterAttempt f n.value d c g
   ⟨prefixRoot a.value,n.work+ch.work+a.work+32⟩
 | .two a b=>let x:=meterAttempt f n.value d c a;let y:=meterAttempt f n.value d c b
   ⟨prefixRoot (combine x.value y.value),n.work+ch.work+x.work+y.work+4*(appendCells x.value+1)+32⟩
 | .refuse why=>⟨⟨[],[why],1,0,0⟩,n.work+ch.work+32⟩
@[simp] theorem meterStep_value (f current d c) :
 (meterStep f current d c).value=CoreProgram.step (fun t d c=>(f t d c).value) current d c := by
 simp only [meterStep,meterNormalize_value,meterChoose_value]
 cases h:choose (normalize current) <;> simp only [h,CoreProgram.step,meterOutput_value,meterAttempt_value]

/-- New explicit local envelope; the frozen localCharge constant is unchanged.
The following bound is derived from the source helpers, not assumed from it. -/
def localCap (N : Nat) : Nat:=1024*(N+1)^3

theorem meterStep_bound (f : GTree→List Group→List RMAF.Vertex→Charged Receipt)
 (t : GTree) (d : List Group) (c : List RMAF.Vertex) (N B R : Nat)
 (tn : footprint t≤N) (dn : d.length≤N) (cn : c.length≤N) (rp : 1≤R)
 (callback : ∀g next,CoreProgram.erase g.origin (normalize t)=some next →
   (f next (g::d) (g.origin::c)).work≤B)
 (recordcap : ∀t d c,records (f t d c).value≤R) :
 (meterStep f t d c).work≤localCap N+2*B+4*(R+1) := by
 have nn:=Nat.le_trans (normalize_footprint t) tn
 have n0:=meterNormalize_bound t N tn
 have n1:=Nat.mul_le_mul_left (32*(N+1)) (Nat.le_trans tn (Nat.le_succ N))
 have nc:=cap_lift N 32 2 3 _ (Nat.le_trans n0 (by simpa only [Nat.pow_two,Nat.mul_assoc] using n1)) (by decide)
 have choose:=meterChoose_bound (normalize t) N nn
 have pos : 1≤(N+1)^3:=Nat.one_le_pow _ _ (by omega)
 have attempts (g : Group) (gn : g.origin.length≤N) :
  (meterAttempt f (normalize t) d c g).work≤B+128*(N+1)^3 := by
  have h:=meterAttempt_bound f (normalize t) d c g N B nn cn gn (callback g)
  have lift:=Nat.mul_le_mul_left 128 (pow_mono N 2 3 (by decide));omega
 simp only [meterStep,meterNormalize_value,meterChoose_value,localCap]
 cases h:CoreProgram.choose (normalize t) with
 | finish=>have out:=meterOutput_bound (normalize t) d c N nn dn;simp only [h];omega
 | refuse why=>simp only [h];omega
 | one g=>
  have gn:=Nat.le_trans (choose_one_origin (normalize t) g h) nn
  have a:=attempts g gn;simp only [h];omega
 | two a b=>
  have origins:=choose_two_origins (normalize t) a b h
  have ac:=attempts a (Nat.le_trans origins.1 nn)
  have bc:=attempts b (Nat.le_trans origins.2 nn)
  have rs:=meterAttempt_records f (normalize t) d c a R rp recordcap
  change appendCells (meterAttempt f (normalize t) d c a).value≤R at rs
  simp only [h];omega
end OrdinaryDispatch.RecoveryLocalWork
