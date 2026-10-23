from pathlib import Path
import os,json,hashlib,subprocess,time
import caller_ledger as ref
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent;iso=b/'isolated'
cs=json.loads((b/'CONTROL-PIN.json').read_text())['controls']
def ls(xs,f=str):return '['+','.join(f(x) for x in xs)+']'
def tr(t):return '(.leaf '+str(t)+')' if isinstance(t,int) else '(.node '+tr(t[0])+' '+tr(t[1])+')'
def ad(p):return ls(p,lambda s:'true' if s=='1' else 'false')
def loc(d):return '(.joint '+ad(d.get('v',''))+' '+ad(d['w'])+')' if d.get('mode')=='joint' else '(.single '+ad(d.get('v',''))+')'
def col(d):return '(⟨'+','.join(loc(d) if i==d.get('active',0) else '.keep' for i in range(3))+'⟩ : Colors)'
header='''import Lean
import WorkControls
open Lean RMAF VertexGeometry Universal233.CoreProgram Universal233.CoreWork Universal233.WholeSourceMass Universal233.WholeSourceWork
 def ja (v : RMAF.Vertex) : String := String.ofList (v.map (fun b => if b then '1' else '0'))
 def jo (o : Output) : Json := Json.mkObj [("partition",toJson o.partition),("cuts",toJson (o.sourceCuts.map ja))]
 def ownedEmpty : Owned := ⟨[],0,0,0,0⟩
 def jdesc (v w : RMAF.Vertex) (c : Colors) : Json :=
   toJson (([(0,c.a),(1,c.b),(2,c.c)]).filterMap (fun (i,l) => match l with
   | .keep => none
   | .single p => some (toJson [toJson "local",toJson i,toJson (if p=v then "v" else "w")])
   | .joint _ _ => some (toJson [toJson "joint",toJson i,toJson "v",toJson "w"])))
 def reviewEmit (id : String) (value metrics : Json) : IO Unit := IO.println ("WHOLE_VALUE "++(Json.mkObj [("id",toJson id),("value",value),("metrics",metrics)]).compress)
'''
lines=[header];expect=[];mapping_rows=[]
for c in cs:
 d=c['input'];op=c['op'];r=ref.evaluate(c);v=r['value'];pre=[];value='Json.null';metrics=[];want=None;note='frozen literal semantic projection'
 if op=='callbacks':
  pre=['let T : Tree := '+tr(d['target']),'let c : Colors := '+col(d)]
  expr='(('+ls(d['queries'])+' : List Nat).map (fun x => (meterTagged T '+ls(d['parents'][0])+' '+ls(d['parents'][1])+' c x).value))';value='toJson '+expr
  invalid=[tag for tag in v['tags'] if isinstance(tag,dict)]
  if invalid:
   # Literal fallbacks independently expanded from source definitions, not observed outputs.
   fallbacks={'overlapping-parent-invalid-not-first-owner':[9],'missing-parent-invalid-not-default-residue':[2],'missing-target-label-lookup-refusal':[9],'nonvertex-target-not-silently-original-region':[6]}
   want=fallbacks[c['id']];note='frozen invalid-domain detector; candidate total fallback observed separately, not asserted to validate premise'
  else:
   want=[]
   for tag in v['tags']:
    if tag[0]=='residue':want.append(tag[1])
    elif tag[0]=='local':want.append(3*tag[1]+d.get('active',0))
    else:want.append(3*(4*tag[1]+tag[2])+d.get('active',0))
  metrics=[('taggedCap','taggedCap T '+ls(d['parents'][0])+' '+ls(d['parents'][1])+' c')]
 elif op=='lookup':
  value='toJson (('+ls(d['queries'])+' : List Nat).map (fun x => ja ((meterLeafList [x] '+tr(d['target'])+').value.headD [])))';want=v['addresses']
 elif op=='hull':value='toJson ((meterMinimal '+ls(d['selected'])+' '+tr(d['target'])+').value.map ja)';want=v['hull']
 elif op=='regions':
  value='toJson ((meterJointColors '+ls(d['selected'])+' '+tr(d['target'])+' '+ad(d['v'])+' '+ad(d['w'])+').value.map (fun (p : Nat×Nat) => [p.1,p.2]))';want=v['distinct_joint']
  metrics=[('work','(meterJointColors '+ls(d['selected'])+' '+tr(d['target'])+' '+ad(d['v'])+' '+ad(d['w'])+').work')]
 elif op=='selector':
  pre=['let r := meterCliqueSelection '+tr(d['target'])+' '+ls(d['parents'][0])+' '+ls(d['parents'][1])+' '+ls(d['parents'][2])]
  value='toJson (r.value.map ja)';want=v['triple_overlap'][0] if v['triple_overlap'] else None;metrics=[('work','r.work')]
 elif op=='schedule':
  pre=['let v : RMAF.Vertex := [false]','let w : RMAF.Vertex := [true]']
  if d['family']=='clique':pre+=['let cs := cliqueColors v'];value='toJson [jdesc v w cs.1,jdesc v w cs.2.1,jdesc v w cs.2.2]'
  else:
   pre+=['let cs := chainColors v w'];value='toJson '+('[jdesc v w cs.1,jdesc v w cs.2.1,jdesc v w cs.2.2.1,jdesc v w cs.2.2.2]' if d['family']=='chain' else '[jdesc v w cs.2.1,jdesc v w cs.2.2.1]')
  want=v['alternatives']
 elif op=='outer':
  objects=[]
  for xs in d['outputs']:
   for x in xs:
    if x not in objects:objects.append(x)
  def ids(xs):return [objects.index(x) for x in xs]
  def own(xs):return '(⟨'+ls(ids(xs),lambda i:'(⟨[['+str(i)+']],[]⟩ : Output)')+',0,0,0,0⟩ : Owned)'
  pre=['let lists : List Owned := '+ls(d['outputs'],own)]
  fold='lists.foldl (fun a r => appendOwned a r) ownedEmpty' if d.get('association','left')=='left' else 'lists.foldr appendOwned ownedEmpty'
  pre+=['let r := '+fold]
  value='toJson (r.outputs.map (fun (o : Output) => (o.partition.headD []).headD 0))';want=ids(v['raw']);metrics=[('copied','r.copied'),('work','r.work')]
 elif op=='generate':
  pre=['let one := meterWhole '+tr(d['source'])+' '+tr(d['target'])+' '+ls(d['parents'][0])+' '+ls(d['parents'][1])+' '+col(d)+' '+str(d['budget']), 'let rs : List Owned := List.replicate '+str(len(v['trace']))+' one','let r := rs.foldl (fun a x => appendOwned a x) ownedEmpty']
  value='Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]'
  want={'outputs':v['raw_outputs'],'colorCalls':r['counts'].get('callback.invocations',0),'pruned':v['pruned']};metrics=[('copied','r.copied'),('work','r.work')]
 mt='Json.mkObj ['+','.join('('+json.dumps(k)+',toJson ('+e+'))' for k,e in metrics)+']'
 lines.append('#eval do\n  '+'\n  '.join(pre+['reviewEmit '+json.dumps(c['id'])+' ('+value+') ('+mt+')']))
 expect.append({'id':c['id'],'expected':want,'scope':note,'frozen_case_id':c['id']})
 mapping_rows.append({'id':c['id'],'operation':op,'frozen_counts':r['counts'],'relation':note})
# Supplemental actual macro outputs are hand-expanded from frozen3/4/2 semantic alternatives and original two-leaf source rules.
A={'partition':[[0],[1]],'cuts':['0']};H={'partition':[[0,1]],'cuts':[]}
for family in ['clique','chain','joint']:
 for q in [0,1]:
  n={'clique':3,'chain':4,'joint':2}[family];name='actual-'+family+'-q'+str(q)
  outs=({'clique':[H,A,A],'chain':[H,H,A,A],'joint':[H,A]}[family] if q==1 else {'clique':[H],'chain':[H,H],'joint':[H]}[family])
  pruned=0 if q==1 else {'clique':2,'chain':2,'joint':1}[family]
  fn={'clique':'meterClique','chain':'meterChain','joint':'meterDiagonal'}[family]
  args='(.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) [0,1] [] [] '+('[] ' if family!='clique' else '')+str(q)
  lines.append('#eval do\n  let r := '+fn+' '+args+'\n  reviewEmit '+json.dumps(name)+' (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson r.copied),("work",toJson r.work)])')
  expect.append({'id':name,'expected':{'outputs':outs,'colorCalls':2*n,'pruned':pruned},'scope':'supplemental post-release hand expansion; actual descriptor association, unchanged source/q; not a changed frozen same-callback fixture'})
# Exact maxima are independently literal (local self=3,joint self=15,parentC joint self=47).
for name,expr,want in [('local-max3','colorLabel (.leaf 0) [] 0',3),('joint-max15','jointLabel (.leaf 0) [] [] 0',15),('tagged-max47','colors (.leaf 0) [] [] ⟨.keep,.keep,.joint [] []⟩ 0',47)]:
 lines.append('#eval reviewEmit '+json.dumps(name)+' (toJson ('+expr+')) (Json.mkObj [])');expect.append({'id':name,'expected':want,'scope':'supplemental explicit source-derived maximum witness'})
s='\n\n'.join(lines)+'\n';source=iso/'WholeReviewValuesV2.lean';source.write_text(s)
pin={'phase':'post-release explicit adapter pinned BEFORE candidate value execution; frozen34 cases/93 plants unchanged','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'translation':'reference local/joint signatures encode candidate3*local+parent; invalid finite-graph/parent domains are explicit premise failures and separately total fallback, not forced candidate refusals','expectations':expect,'relations':mapping_rows,'supplemental_expected_not_from_candidate_outputs':True}
(b/'VALUE-ADAPTER-PIN-v2.json').write_text(json.dumps(pin,indent=2)+'\n')
env=os.environ.copy();env['LEAN_PATH']=str(iso);t=time.monotonic();p=subprocess.run([str(root/'bootloops-lean'),'WholeReviewValuesV2.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=45);log=b/'WholeReviewValuesV2.log';log.write_text(p.stdout);assert p.returncode==0,p.stdout
rows=[json.loads(x.split('WHOLE_VALUE ',1)[1]) for x in p.stdout.splitlines() if 'WHOLE_VALUE ' in x];assert len(rows)==len(expect),(len(rows),len(expect))
for e,r in zip(expect,rows):assert e['id']==r['id'] and e['expected']==r['value'],(e,r)
result={'status':'PASS-FROZEN-SEMANTIC-ADAPTER-AND-SUPPLEMENTAL-VALUES','comparisons':len(rows),'frozen_case_relations':len(cs),'supplemental_actual_macro_cases':6,'maximum_witnesses':3,'seconds':time.monotonic()-t,'source_sha256':pin['source_sha256'],'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'observations':rows,'expectation_provenance':pin['phase']}
(b/'VALUE-COMPARISON.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='observations'}))
