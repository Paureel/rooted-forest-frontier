#!/usr/bin/env python3
"""One-shot actual compiled-definition adapter against untouched frozen graph controls."""
import argparse,json,os,pathlib,subprocess,sys,time
HERE=pathlib.Path(__file__).resolve().parent; ROOT=HERE.parents[5]; B=HERE/'isolated'; FROZEN=HERE.parent/'sol-frozen-ready-v1'/'preparation';sys.path.insert(0,str(FROZEN))
from graph_controls_v1 import Graph,labels,forests,partitions,proper,ready,agrees,cost,cleanup,coalesce,contract_block,expand_block,canonical,compare_record
from transport_mutations_v1 import expand_tree
LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
def tree(t):
 if t is None:return 'none'
 if isinstance(t,int):return f'(RMAF.Tree.leaf {t})'
 return f'(RMAF.Tree.node {tree(t[0])} {tree(t[1])})'
def opt(t):return 'none' if t is None else '(some '+tree(t)+')'
def natlist(xs):return '['+','.join(str(x) for x in xs)+']'
def forest(F):return '['+','.join(natlist(B) for B in F)+']'
def treelist(ss):return '['+','.join(tree(s) for s in ss)+']'
def norm_forest(F):return sorted([sorted(B) for B in F])
def main():
 p=argparse.ArgumentParser();p.add_argument('--pilot',action='store_true');a=p.parse_args();spec=json.loads((FROZEN/'EXPECTATIONS-v1.json').read_text()); fixtures=spec['fixtures'][:4] if a.pilot else spec['fixtures']; lines=[]; native=[]; expected=[]
 def row(kind,ident,fields,expect,normalize=()):
  native.append('Json.mkObj [('+', '.join(f'("{k}", {v})' for k,v in [('kind',f'Json.str "{kind}"'),('id',f'Json.str "{ident}"')]+list(fields.items())))+')]')
  expected.append({'kind':kind,'id':ident,**expect,'_normalize':list(normalize)})
 for i,f in enumerate(fixtures):
  T,ss,aa,bb,z=(f[k] for k in ('T','ss','a','b','z'));tn=f't{i}';sn=f's{i}'; pn=f'p{i}';lines += [f'def {tn} : Option Tree := {opt(T)}',f'def {sn} : List Tree := {treelist(ss)}',f'def {pn} : List (List (List Nat)) := {forest_family(list(partitions(labels(T))))}']
  P=list(partitions(labels(T))); FF=forests(T,ss)
  fields={'proper':f'toJson (proper {tn} {sn})','ready':f'toJson (cherryReady {tn} {sn} {aa} {bb} {z})','labels':f'toJson (labels {tn})','validity':f'toJson ({pn}.map (agrees {tn} {sn}))','validCosts':f'toJson (({pn}.filter (agrees {tn} {sn})).map (additionalCost {sn}))','qTruth':f'toJson ({natlist(spec["q"])}.map (fun q => {pn}.any (fun F => agrees {tn} {sn} F && decide (additionalCost {sn} F ≤ q))))'}
  ex={'proper':f['proper'],'ready':f['ready'],'labels':labels(T),'validity':[agrees(T,ss,F) for F in P],'validCosts':[cost(ss,F) for F in FF],'qTruth':[f['minimum'] is not None and f['minimum']<=q for q in spec['q']]}
  if 'singleton' in f:
   x=f['singleton'];fields.update({'cleanupT':f'jOpt (cleanupTarget {tn} {x})','cleanupSS':f'jTrees (cleanupSources {sn} {x})'});ex.update({'cleanupT':f['cleanupT'],'cleanupSS':f['cleanupSS']})
  if f['ready']:
   fields.update({'contractT':f'jOpt ({tn}.map (contract {aa} {bb} {z}))','contractSS':f'jTrees ({sn}.map (contract {aa} {bb} {z}))','expandedT':f'jOpt (({tn}.map (contract {aa} {bb} {z})).map (expand {aa} {bb} {z}))','expandedSS':f'jTrees (({sn}.map (contract {aa} {bb} {z})).map (expand {aa} {bb} {z}))'})
   ex.update({'contractT':f['contractT'],'contractSS':f['contractSS'],'expandedT':expand_tree(f['contractT'],aa,bb,z),'expandedSS':[expand_tree(s,aa,bb,z) for s in f['contractSS']]})
  row('state',f['id'],fields,ex)
  if T is not None and len(ss)==1 and f['proper']:
   row('initial',f['id'],{'originalValidity':f'toJson ({pn}.map (agreement {tree(T)} {tree(ss[0])}))'},{'originalValidity':[agrees(T,ss,F) for F in P]})
  if 'singleton' in f:
   x=f['singleton'];T2,ss2=f['cleanupT'],f['cleanupSS']
   for j,F in enumerate(FF):
    _,_,F2=cleanup(T,ss,F,x);fn=forest(F);row('singleton-forward',f'{f["id"]}-{j}',{'F':f'toJson (cleanupForest {fn} {x})','valid':f'toJson (agrees (cleanupTarget {tn} {x}) (cleanupSources {sn} {x}) (cleanupForest {fn} {x}))','oldCost':f'toJson (additionalCost {sn} {fn})','newCost':f'toJson (additionalCost (cleanupSources {sn} {x}) (cleanupForest {fn} {x}))'},{'F':F2,'valid':True,'oldCost':cost(ss,F),'newCost':cost(ss2,F2)})
   for j,G in enumerate(forests(T2,ss2)):
    fn=forest([[x]]+G);row('singleton-reverse',f'{f["id"]}-{j}',{'F':f'toJson ({fn} : List (List Nat))','valid':f'toJson (agrees {tn} {sn} {fn})','cost':f'toJson (additionalCost {sn} {fn})'},{'F':[[x]]+G,'valid':True,'cost':cost(ss2,G)})
  if f['ready']:
   T2,ss2=f['contractT'],f['contractSS'];cT=f'({tn}.map (contract {aa} {bb} {z}))';cSS=f'({sn}.map (contract {aa} {bb} {z}))'
   for j,F in enumerate(FF):
    gn=f'g{i}_{j}';G=coalesce(F,aa,bb);H=[contract_block(D,aa,bb,z) for D in G];lines.append(f'def {gn} : List (List Nat) := reviewCoalesce {forest(F)} {aa} {bb}')
    row('cherry-forward',f'{f["id"]}-{j}',{'G':f'toJson {gn}','validG':f'toJson (agrees {tn} {sn} {gn})','oldCost':f'toJson (additionalCost {sn} {forest(F)})','newCost':f'toJson (additionalCost {sn} {gn})','H':f'toJson ({gn}.map (contractBlock {aa} {bb} {z}))','validH':f'toJson (agrees {cT} {cSS} ({gn}.map (contractBlock {aa} {bb} {z})))','costH':f'toJson (additionalCost {cSS} ({gn}.map (contractBlock {aa} {bb} {z})))'},{'G':G,'validG':True,'oldCost':cost(ss,F),'newCost':cost(ss,G),'H':H,'validH':True,'costH':cost(ss,G)},normalize=('G','H'))
   for j,G in enumerate(forests(T2,ss2)):
    H=[expand_block(D,aa,bb,z) for D in G];row('cherry-reverse',f'{f["id"]}-{j}',{'F':f'toJson ({forest(G)}.map (expandBlock {aa} {bb} {z}))','valid':f'toJson (agrees {tn} {sn} ({forest(G)}.map (expandBlock {aa} {bb} {z})))','cost':f'toJson (additionalCost {sn} ({forest(G)}.map (expandBlock {aa} {bb} {z})))','contractBack':f'toJson (({forest(G)}.map (expandBlock {aa} {bb} {z})).map (contractBlock {aa} {bb} {z}))'},{'F':H,'valid':True,'cost':cost(ss2,G),'contractBack':G})
 if not a.pilot:
  byid={f['id']:f for f in fixtures}
  for j,e in enumerate(spec['agreements']):
   f=byid[e['fixture']];row('explicit-forest',str(j),{'valid':f'toJson (agrees {opt(f["T"])} {treelist(f["ss"])} {forest(e["F"])})','cost':f'toJson (additionalCost {treelist(f["ss"])} {forest(e["F"])})'},{'valid':e['valid'],'cost':e['cost']})
  for g in spec['geometry']:
   fields={'hull':f'toJson ((minimalVertices {natlist(g["B"])} {tree(g["T"])}).map (fun v => String.ofList (v.map (fun b => if b then \'1\' else \'0\'))))','restriction':f'jOpt (restrict {natlist(g["B"])} {tree(g["T"])})'};ex={'hull':g['hull'],'restriction':g['restriction']}
   if 'C' in g:
    fields.update({'disjoint':f'toJson (disjointVertices (minimalVertices {natlist(g["B"])} {tree(g["T"])}) (minimalVertices {natlist(g["C"])} {tree(g["T"])}))','addedDisjoint':f'toJson (disjointVertices (minimalVertices {natlist(g["addedB"])} {tree(g["T"])}) (minimalVertices {natlist(g["C"])} {tree(g["T"])}))'});ex.update({'disjoint':g['disjoint'],'addedDisjoint':g['addedDisjoint']})
   row('geometry',g['id'],fields,ex,normalize=('hull',))
 header='''import CompletionConsumers
import Consumers
import Lean
open Lean RMAF ForestState
namespace SolReadouts
def jTree : Tree → Json
  | .leaf x => toJson x
  | .node l r => Json.arr #[jTree l,jTree r]
def jOpt : Option Tree → Json
  | none => Json.null
  | some t => jTree t
def jTrees (ss : List Tree) : Json := Json.arr (ss.map jTree).toArray
-- Declared literal/case adapter: theorem chooses unique a-owner and swaps if singleton.
def reviewCoalesce (F : List (List Nat)) (a b : Nat) : List (List Nat) :=
  let A := (F.find? (fun B => B.contains a)).getD []
  let B := (F.find? (fun B => B.contains b)).getD []
  if A.contains b then F else
    if A == [a] then reassignedForest F B a else reassignedForest F A b
'''
 name='NativePilot' if a.pilot else 'NativeFull'; source=header+'\n'.join(lines)+'\n#eval IO.println (Json.arr #[\n'+',\n'.join(native)+'\n]).compress\nend SolReadouts\n'; (B/(name+'.lean')).write_text(source);(HERE/(name+'-expected.json')).write_text(json.dumps(expected,indent=2)+'\n')
 t=time.perf_counter();r=subprocess.run([str(LEAN),name+'.lean'],cwd=B,env={**os.environ,'LEAN_PATH':str(B)},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60);(HERE/(name+'.log')).write_text(r.stdout);assert r.returncode==0,r.stdout
 actual=json.loads(next(l for l in r.stdout.splitlines() if l.startswith('[{')));compare_record(len(actual),len(expected));counts={}
 for got,want in zip(actual,expected):
  normal=want.pop('_normalize')
  for k in normal:
   if k=='hull':got[k]=sorted(got[k]);want[k]=sorted(want[k])
   else:got[k]=norm_forest(got[k]);want[k]=norm_forest(want[k])
  compare_record(got,want);counts[got['kind']]=counts.get(got['kind'],0)+1
 result={'status':'NATIVE-COMPARISONS-PASS','records':len(actual),'counts':counts,'seconds':time.perf_counter()-t,'frozenExpectedSource':str(FROZEN),'expectedValuesRetuned':False,'nativeRows':actual};(HERE/(name+'-result.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='nativeRows'}))
def forest_family(Fs):return '['+','.join(forest(F) for F in Fs)+']'
if __name__=='__main__':main()
