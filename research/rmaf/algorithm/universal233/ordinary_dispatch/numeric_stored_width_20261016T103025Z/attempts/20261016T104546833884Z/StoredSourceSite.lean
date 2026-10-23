import StoredBudget
import BuildIdentity
namespace OrdinaryDispatch.StoredNumeric
open RMAF Universal233.WholeSourceWork Universal233.CoreWork
open GenericForest.ScalarBits GenericForest.BinaryProvider

/-- All eight payload operands and both markers equal the fields of the actual
checked source Setup. The two scalar representative equations are explicit
selector-producer obligations, rather than decoded-value runtime conversions. -/
theorem commonPayload_source_site (T S : GenericForest.BinaryProvider.Tree) (X Y : Block) (x y : Bits)
 (p : RMAF.Vertex) (d : OrdinaryCommonSplit.Caller.Setup)
 (built : OrdinaryCommonSplit.Source.buildSetup (treeValue T) (treeValue S) (blockValue X) (blockValue Y) p=some d)
 (hx : decode x=d.x) (hy : decode y=d.y) :
 let out:=(commonPayloadBits T S X Y x y).value
 decode out.rho=d.rho ∧ decode out.gamma=d.gamma ∧
 [targetValue out.tx,targetValue out.sx,targetValue out.ty,targetValue out.sy,
  targetValue out.mxT,targetValue out.mxS,targetValue out.myT,targetValue out.myS]=
 [some d.tx,some d.sx,some d.ty,some d.sy,some d.mxT,some d.mxS,some d.myT,some d.myS] := by
 have ids:=OrdinaryCommonSplit.Source.buildSetup_identity (treeValue T) (treeValue S) (blockValue X) (blockValue Y) p d built
 have fresh:=freshPair_source_site T S (blockValue X) (blockValue Y) p d built
 obtain ⟨tx,sx,ty,sy,mxt,mxs,myt,mys⟩:=commonPayloadBits_value T S X Y x y
 dsimp only
 refine ⟨fresh.1,fresh.2,?_⟩
 rw [tx,sx,ty,sy,mxt,mxs,myt,mys,fresh.1,fresh.2,hx,hy]
 rw [←ids.1,←ids.2.1,←ids.2.2.1,←ids.2.2.2]
 rw [d.htx,d.hsx,d.hty,d.hsy,d.hMXT,d.hMXS,d.hMYT,d.hMYS]

/-- Original-input local fees after the StoredPath/semantic-trace depth binding
has been established by a complete producer. B is the actual initial stored
label width. The fee arguments remain explicit polynomials in B,N,Q. -/
theorem global_common_payload_fee (B N Q : Nat) (T0 S0 : GenericForest.BinaryProvider.Tree)
 (proper0 : Universal233.DepthOne.proper (treeValue T0) (treeValue S0)=true)
 (size0 : (leaves (treeValue T0)).length≤N) (tc0 : TreeWidth B T0) (sc0 : TreeWidth B S0)
 {d T S} (path : StoredPath T0 S0 d T S) (depth : d≤Q+N)
 (X Y : Block) (x y : Bits) (xl : X.length≤N) (yl : Y.length≤N)
 (xc : BlockWidth (stateStorageWidth B N Q) X) (yc : BlockWidth (stateStorageWidth B N Q) Y)
 (hx : x.length≤stateStorageWidth B N Q) (hy : y.length≤stateStorageWidth B N Q) :
 (commonPayloadBits T S X Y x y).work≤commonPayloadFee (2*N) N (stateStorageWidth B N Q) := by
 have caps:=global_storage_caps B N Q T0 S0 proper0 size0 tc0 sc0 path depth
 exact commonPayloadBits_work (2*N) N (stateStorageWidth B N Q) T S X Y x y
  caps.2.2.1 caps.2.2.2.1 xl yl caps.1 caps.2.1 xc yc hx hy
end OrdinaryDispatch.StoredNumeric
