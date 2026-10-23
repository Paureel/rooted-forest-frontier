from pathlib import Path
import json,subprocess,os,hashlib,time
import work_ledger as ref
root=Path(__file__).resolve().parents[5];base=Path(__file__).resolve().parent;iso=base/'isolated'
controls=json.loads((base/'CONTROL-PIN.json').read_text())['controls']
def ls(xs,f=str):return '['+','.join(f(x) for x in xs)+']'
def tree(t):return '(.leaf '+str(t)+')' if isinstance(t,int) else '(.node '+tree(t[0])+' '+tree(t[1])+')'
def addr(p):return ls(p,lambda c:'true' if c=='1' else 'false')
def color(d):
 c=d.get('colors',{'kind':'id'})
 if c['kind']=='id':return '(fun x : Nat => x)'
 if c['kind']=='constant':return '(fun _ : Nat => '+str(c['value'])+')'
 return '(fun x : Nat => '+''.join('if x = '+str(i)+' then '+str(v)+' else ' for i,v in enumerate(c['values']))+'0)'
def current(d):
 e='(fromTree '+color(d)+' '+addr(d.get('prefix',''))+' '+tree(d['tree'])+')'
 return '(normalize '+e+')' if d.get('normalize_input') else e
header='''import Lean
import Controls
open Lean RMAF Universal233.CoreProgram Universal233.CoreWork

def jAddr (v : Vertex) : String := String.ofList (v.map (fun b => if b then '1' else '0'))
def jGroup (g : Group) : Json := Json.arr #[toJson (jAddr g.origin),toJson g.labels,toJson g.color]
def jView (t : Option GTree) : Json := match t with
  | none => Json.mkObj [("root",Json.null),("groups",toJson ([] : List Json))]
  | some t => Json.mkObj [("root",toJson (jAddr (match t with | .leaf g => g.origin | .node p _ _ => p))), ("groups",toJson ((groups t).map jGroup))]
def jReceipt (r : Receipt) : Json := Json.mkObj [
  ("outputs",toJson (r.outputs.map (fun o => Json.mkObj [("partition",toJson o.partition),("cuts",toJson (o.sourceCuts.map jAddr))]))),
  ("refusals",toJson r.refusals),("visited",toJson r.visited),("childAttempts",toJson r.childAttempts),("pruned",toJson r.pruned)]
def jChoice (c : Choice) : Json := match c with
  | .finish => Json.mkObj [("kind",toJson "finish"),("origins",toJson ([] : List String))]
  | .one a => Json.mkObj [("kind",toJson "one"),("origins",toJson [jAddr a.origin])]
  | .two a b => Json.mkObj [("kind",toJson "two"),("origins",toJson [jAddr a.origin,jAddr b.origin])]
  | .refuse why => Json.mkObj [("kind",toJson "refuse"),("refusals",toJson [why])]
def emitReview (id : String) (value metrics : Json) : IO Unit := IO.println ("LEDGER_COMPARE "++(Json.mkObj [("id",toJson id),("value",value),("metrics",metrics)]).compress)
'''
lines=[header];expected={};reports={}
for i,c in enumerate(controls):
 d=c['input'];op=c['op'];report=ref.evaluate(c);reports[c['id']]=report
 val='Json.null';metrics=[];preamble=[]
 if op=='append':val='toJson (('+ls(d['left'])+' : List Nat) ++ '+ls(d['right'])+')'
 elif op=='combine':
  def receipt(x):return '(⟨List.replicate '+str(len(x['outputs']))+' ⟨[],[]⟩,'+ls(x['refusals'],json.dumps)+','+str(x.get('visited',0))+','+str(x.get('attempts',0))+','+str(x.get('pruned',0))+'⟩ : Receipt)'
  preamble=['let a := '+receipt(d['left']),'let b := '+receipt(d['right']),'let r := combine a b']
  val='Json.mkObj [("outputs_length",toJson r.outputs.length),("refusals_length",toJson r.refusals.length),("visited",toJson r.visited),("childAttempts",toJson r.childAttempts),("pruned",toJson r.pruned)]'
  metrics=[('copied','appendCells a')]
 elif op=='fromTree':
  preamble=['let r := meterFromTree '+color(d)+' '+addr(d.get('prefix',''))+' '+tree(d['tree'])]
  val='jView (some r.tree)';metrics=[('oracleCalls','r.oracleCalls'),('footprint','footprint r.tree')]
 else:
  preamble=['let t := '+current(d)]
  if op=='normalize':val='jView (some (normalize t))';metrics=[('normalizeWork','normalizeWork t')]
  elif op=='groups':val='toJson ((groups t).map jGroup)';metrics=[('groupsWork','groupsWork t')]
  elif op=='erase':val='jView (erase '+addr(d['chosen'])+' t)';metrics=[('eraseWork','eraseWork '+addr(d['chosen'])+' t')]
  elif op=='choose':val='jChoice (choose t)';metrics=[('findFilterWork','findFilterWork (groups t) (groups t)')]
  elif op=='attempt':
   g=d['group'];preamble+=['let g : Group := ⟨'+addr(g[0])+','+ls(g[1])+','+str(g[2])+'⟩','let r := meterAttempt (fun _ _ _ => ⟨⟨[],[],0,0,1⟩,1,0,1⟩) t [] '+ls(d.get('cuts',[]),addr)+' g']
   val='jReceipt r.receipt';metrics=[('work','r.work'),('prunedCalls','r.prunedCalls')]
  elif op=='run':
   preamble+=['let r := meterRun '+str(d['budget'])+' t [] []'];val='jReceipt r.receipt';metrics=[('work','r.work'),('copied','r.copied'),('prunedCalls','r.prunedCalls')]
  elif op=='generate':
   preamble=['let t : Tree := '+tree(d['tree']),'let r := meterGenerate t '+color(d)+' '+str(d['budget'])]
   val='jReceipt r.measured.receipt';metrics=[('work','r.measured.work'),('copied','r.measured.copied'),('prunedCalls','r.measured.prunedCalls'),('oracleCalls','r.oracleCalls'),('initialCharge','initialCharge t'),('N','treeNodes t'),('B','min '+str(d['budget'])+' ((leaves t).length-1)')]
 mt='Json.mkObj ['+','.join('('+json.dumps(k)+',toJson ('+v+'))' for k,v in metrics)+']'
 lines.append('#eval do\n  '+'\n  '.join(preamble+['emitReview '+json.dumps(c['id'])+' ('+val+') ('+mt+')']))
(iso/'ReviewLedgerValuesV2.lean').write_text('\n\n'.join(lines)+'\n')
env=os.environ.copy();env['LEAN_PATH']=str(iso);t=time.monotonic()
p=subprocess.run([str(root/'bootloops-lean'),'ReviewLedgerValuesV2.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
log=base/'ReviewLedgerValuesV2.log';log.write_text(p.stdout);assert p.returncode==0,p.stdout
rows=[json.loads(x.split('LEDGER_COMPARE ',1)[1]) for x in p.stdout.splitlines() if 'LEDGER_COMPARE ' in x];assert len(rows)==len(controls)
checks=[]
for c,row in zip(controls,rows):
 assert row['id']==c['id'];r=reports[c['id']];v=r['value'];m=row['metrics'];counts=r['counts'];details=[]
 if c['op']=='combine':
  expected={k:len(v[k[:-7]]) if k.endswith('_length') else v[k] for k in row['value']};assert row['value']==expected
 else:assert row['value']==v,(c['id'],row['value'],v)
 details.append('value projection (combine: exact output/refusal lengths and counters)')
 if 'oracleCalls' in m:assert m['oracleCalls']==counts.get('oracle.color_calls',0);details.append('source color calls')
 if 'copied' in m:
  assert m['copied']==counts.get('append.receipt_outputs.left_cells',0)+counts.get('append.receipt_refusals.left_cells',0);details.append('both actual receipt left-copy lengths')
 if 'prunedCalls' in m:assert m['prunedCalls']==counts.get('prune.callback',0);details.append('pruned continuation calls')
 for key,event in [('normalizeWork','append.normalize_payload.left_cells'),('groupsWork','append.groups.left_cells')]:
  if key in m:assert m[key]>=counts.get(event,0);details.append(key+' dominates literal copied cells (not fine-unit time equality)')
 checks.append({'id':c['id'],'observed_metrics':m,'independent_counts':counts,'checks':details,'structural_vector_not_machine_time':True})
result={'status':'PASS-FROZEN-LITERAL-COMPARISON','cases':len(checks),'seconds':time.monotonic()-t,'source_sha256':hashlib.sha256((iso/'ReviewLedgerValuesV2.lean').read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'checks':checks,'scope':'Finite source-value, oracle/prune/copy comparisons to frozen independent ledgers. Domination/source correspondence handled separately; no equality of scalar work with machine operations.'}
(base/'LEDGER-COMPARISON.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='checks'}))
