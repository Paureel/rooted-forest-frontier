import SetupAtoms
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
namespace Universal233.Rule5RemainingLocalWork
open RMAF CoreGraph HardParent CoreWork Rule5PrefixLocalWork Rule5PendantLocalWork
open GenericForest.CheckCorrespondence OrdinaryCommonSplit OrdinaryCommonSplit.Source OrdinaryCommonSplit.Caller
open RestrictionBridge

/-- Literal dependent builder with costs on each executed guard and refusal path.
The two labelMax occurrences and eight separate restrictions are retained. -/
def setupMeter (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) : Measured (Option Setup) :=
  bump ((nodupTreeMeter T).work+1) <|
  if nt : (leaves T).Nodup then
  bump ((nodupTreeMeter S).work+1) <|
  if ns : (leaves S).Nodup then
  bump ((partitionTreeMeter T X Y).work+1) <|
  if hpT : partitionCheck (leaves T) [X,Y]=true then
  bump ((partitionTreeMeter S X Y).work+1) <|
  if hpS : partitionCheck (leaves S) [X,Y]=true then
  bump 2 <|
  if nonroot : p≠[] then
  bump ((subtreeMeter S p).work+1) <|
  match source : subtree S p with
  | none => ⟨none,1⟩
  | some u =>
    bump ((leavesMeter u).work+(permMeter (leaves u) X).work+1) <|
    if labels : (leaves u).Perm X then
    bump ((incidentMeter T X).work+1) <|
    match boundary : incident T X with
    | [q] =>
      let x := X.headD 0
      let y := Y.headD 0
      let L := leaves T++leaves S
      let rho := labelMax L+1
      let gamma := labelMax L+2
      bump ((leavesMeter T).work+(leavesMeter S).work+(leaves T).length+
        2*(maxMeter L).work+8+
        (meterRestrict X T).work+(meterRestrict X S).work+
        (meterRestrict Y T).work+(meterRestrict Y S).work+
        (markedMeter T X y rho).work+(markedMeter S X y rho).work+
        (markedMeter T Y x gamma).work+(markedMeter S Y x gamma).work+8) <|
      match htx : restrict X T, hsx : restrict X S,
            hty : restrict Y T, hsy : restrict Y S,
            hMXT : marked T X y rho, hMXS : marked S X y rho,
            hMYT : marked T Y x gamma, hMYS : marked S Y x gamma with
      | some tx,some sx,some ty,some sy,some mxT,some mxS,some myT,some myS =>
        ⟨some {
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
          fgS:=fun h=>fresh_not_mem L 2 (by decide) (List.mem_append_right _ h) },1⟩
      | _,_,_,_,_,_,_,_ => ⟨none,1⟩
    | _ => ⟨none,1⟩
    else ⟨none,1⟩
  else ⟨none,1⟩
  else ⟨none,1⟩
  else ⟨none,1⟩
  else ⟨none,1⟩
  else ⟨none,1⟩

theorem setup_value (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) :
 (setupMeter T S X Y p).value=buildSetup T S X Y p := by
 by_cases nt : (leaves T).Nodup
 · by_cases ns : (leaves S).Nodup
   · by_cases hpT : partitionCheck (leaves T) [X,Y]=true
     · by_cases hpS : partitionCheck (leaves S) [X,Y]=true
       · by_cases nonroot : p≠[]
         · cases source : subtree S p with
           | none=>simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source]
           | some u=>
             by_cases labels : (leaves u).Perm X
             · cases boundary : incident T X with
               | nil=>simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source,labels,boundary]
               | cons q qs=>
                 cases qs with
                 | nil=>
                   cases htx : restrict X T with
                   | none=>simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source,labels,boundary,htx]
                   | some tx=>
                     cases hsx : restrict X S with
                     | none=>simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source,labels,boundary,htx,hsx]
                     | some sx=>
                       cases hty : restrict Y T with
                       | none=>simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source,labels,boundary,htx,hsx,hty]
                       | some ty=>
                         cases hsy : restrict Y S with
                         | none=>simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source,labels,boundary,htx,hsx,hty,hsy]
                         | some sy=>
                           cases hMXT : marked T X (Y.headD 0) (labelMax (leaves T++leaves S)+1) with
                           | none=>simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source,labels,boundary,htx,hsx,hty,hsy,hMXT]
                           | some mxT=>
                             cases hMXS : marked S X (Y.headD 0) (labelMax (leaves T++leaves S)+1) with
                             | none=>simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source,labels,boundary,htx,hsx,hty,hsy,hMXT,hMXS]
                             | some mxS=>
                               cases hMYT : marked T Y (X.headD 0) (labelMax (leaves T++leaves S)+2) with
                               | none=>simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source,labels,boundary,htx,hsx,hty,hsy,hMXT,hMXS,hMYT]
                               | some myT=>
                                 cases hMYS : marked S Y (X.headD 0) (labelMax (leaves T++leaves S)+2) with
                                 | none=>simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source,labels,boundary,htx,hsx,hty,hsy,hMXT,hMXS,hMYT,hMYS]
                                 | some myS=>
                                   simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source,labels,boundary,htx,hsx,hty,hsy,hMXT,hMXS,hMYT,hMYS]
                 | cons r rs=>simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source,labels,boundary]
             · simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot,source,labels]
         · simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS,nonroot]
       · simp [setupMeter,buildSetup,bump,nt,ns,hpT,hpS]
     · simp [setupMeter,buildSetup,bump,nt,ns,hpT]
   · simp [setupMeter,buildSetup,bump,nt,ns]
 · simp [setupMeter,buildSetup,bump,nt]

end Universal233.Rule5RemainingLocalWork
