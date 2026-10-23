import ActualCuts
namespace OrdinaryCommonSplit.Source
open RMAF Universal233 CoreGraph RestrictionBridge Caller

def labelMax (L : List Nat) : Nat := L.foldr Nat.max 0

theorem label_le_max (L : List Nat) (x : Nat) (hx : x∈L) : x≤labelMax L := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

theorem fresh_not_mem (L : List Nat) (i : Nat) (positive : 0<i) : labelMax L+i∉L := by
  intro h
  have bound := label_le_max L _ h
  omega

theorem headD_mem (L : List Nat) (ne : L≠[]) : L.headD 0∈L := by
  cases L with
  | nil => contradiction
  | cons a L => simp

/-- Actual checked construction. All guards and restrictions are executed;
the output proof fields contain only the checked original input facts. -/
def buildSetup (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) : Option Setup :=
  if nt : (leaves T).Nodup then
  if ns : (leaves S).Nodup then
  if hpT : partitionCheck (leaves T) [X,Y]=true then
  if hpS : partitionCheck (leaves S) [X,Y]=true then
  if nonroot : p≠[] then
  match source : subtree S p with
  | none => none
  | some u =>
    if labels : (leaves u).Perm X then
    match boundary : incident T X with
    | [q] =>
      let x := X.headD 0
      let y := Y.headD 0
      let L := leaves T++leaves S
      let rho := labelMax L+1
      let gamma := labelMax L+2
      match htx : restrict X T, hsx : restrict X S,
            hty : restrict Y T, hsy : restrict Y S,
            hMXT : marked T X y rho, hMXS : marked S X y rho,
            hMYT : marked T Y x gamma, hMYS : marked S Y x gamma with
      | some tx,some sx,some ty,some sy,some mxT,some mxS,some myT,some myS =>
        some {
          T:=T,S:=S,tx:=tx,sx:=sx,ty:=ty,sy:=sy,mxT:=mxT,mxS:=mxS,myT:=myT,myS:=myS,
          X:=X,Y:=Y,x:=x,y:=y,rho:=rho,gamma:=gamma,nt:=nt,ns:=ns,hpT:=hpT,hpS:=hpS,
          edgeT:=original_split_from_incident T X Y q nt hpT boundary,
          edgeS:=original_source_split S u X Y p nonroot source labels,
          htx:=htx,hsx:=hsx,hty:=hty,hsy:=hsy,hMXT:=hMXT,hMXS:=hMXS,hMYT:=hMYT,hMYS:=hMYS,
          hx:=headD_mem X (checked_nonempty _ _ hpT X (by simp)),
          hy:=headD_mem Y (checked_nonempty _ _ hpT Y (by simp)),
          frT:=fun h=>fresh_not_mem L 1 (by decide) (List.mem_append_left _ h),
          frS:=fun h=>fresh_not_mem L 1 (by decide) (List.mem_append_right _ h),
          fgT:=fun h=>fresh_not_mem L 2 (by decide) (List.mem_append_left _ h),
          fgS:=fun h=>fresh_not_mem L 2 (by decide) (List.mem_append_right _ h) }
      | _,_,_,_,_,_,_,_ => none
    | _ => none
    else none
  else none
  else none
  else none
  else none
  else none
end OrdinaryCommonSplit.Source
