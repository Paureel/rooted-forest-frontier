"""One-shot source-only replay/all-origin auditor; no author audit code reuse."""
from pathlib import Path
import os,json,re,subprocess,time,hashlib,datetime
b=Path(__file__).resolve().parent;root=b.parents[4];iso=b/'isolated';logs=b/'candidate-logs';logs.mkdir(exist_ok=True)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pin=json.loads((b/'CANDIDATE-PIN.json').read_text());sources={x['module']:iso/(x['module']+'.lean') for x in pin['copied_sources'] if x['positive']}
for x in pin['copied_sources']:assert h(iso/(x['module']+'.lean'))==x['sha256'],x
deps={n:[m for m in re.findall(r'^import\s+(\w+)',p.read_text(),re.M) if m in sources] for n,p in sources.items()};order=[]
def visit(n):
 if n in order:return
 for m in deps[n]:visit(m)
 order.append(n)
for n in sources:visit(n)
env=os.environ.copy();env['LEAN_PATH']=str(iso);rows=[]
def build(n,positive=True):
 t=time.monotonic();r=subprocess.run([str(root/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60);p=logs/(n+'.log');p.write_text(r.stdout);rows.append({'module':n,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':h(iso/(n+'.lean')),'log_sha256':h(p)})
 if positive:assert r.returncode==0,(n,r.stdout)
 return r
for n in order:build(n)
template=(b/'std-toys/CutAudit.lean').read_text().replace('import CutClean\nimport CutUsed\nimport CutUnused','\n'.join('import '+n for n in order)).replace('["CutClean","CutUsed","CutUnused"]',json.dumps(order)).replace('CUT_ORIGIN ','REVIEW_ORIGIN ')
template=template.replace('let row := Json.mkObj', '''let body := c.value? (allowOpaque := true)
    let typeNames := c.type.getUsedConstants.toList.map Name.toString
    let bodyNames := match body with | none => [] | some v => v.getUsedConstants.toList.map Name.toString
    let bodyHash : Json := match body with | none => Json.null | some v => toJson (hash v).toNat
    let row := Json.mkObj''')
template=template.replace('("kind",toJson (toyKind c)),','("kind",toJson (toyKind c)),("type_structural_hash",toJson (hash c.type).toNat),("body_structural_hash",bodyHash),("type_constants",toJson typeNames),("body_constants",toJson bodyNames),')
(iso/'IndependentAudit.lean').write_text(template);r=build('IndependentAudit')
audit=[json.loads(l.split('REVIEW_ORIGIN ',1)[1]) for l in r.stdout.splitlines() if 'REVIEW_ORIGIN ' in l]
assert set(x['origin'] for x in audit)==set(order) and len(audit)==len({x['name'] for x in audit})
allowed={'Classical.choice','Quot.sound','propext'};assert all(x['kind']!='axiom' and set(x['axioms'])<=allowed for x in audit)
neg=[]
for n,expected in [('FalseControl',1),('FalseControls',3)]:
 r=build(n,False);count=r.stdout.count('Tactic `decide` proved that the proposition');assert r.returncode!=0 and count==expected,r.stdout;neg.append({'module':n,'explicit_false_diagnostics':count})
out={'status':'PASS-SOURCE-ONLY-ALL-ORIGIN-REPLAY','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'positive_order':order,'positive_modules':len(order),'declaration_count':len(audit),'private_count':sum('_private.' in x['name'] for x in audit),'module_counts':{n:sum(x['origin']==n for x in audit) for n in order},'axiom_union':sorted({a for x in audit for a in x['axioms']}),'all_origin_records':audit,'builds':rows,'false_propositions':neg,'copied_scientific_oleans':0,'body_hash_note':'Lean Expr structural UInt64 hash,not cryptographic identity; immutable complete module source SHA binds exact bodies. Direct type/body constant references and every origin/private/generated record retained.','author_interface_printing':'Interfaces excluded from scientific62,not executed','extra_replications':0}
(b/'REPLAY.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['all_origin_records','builds','module_counts','positive_order']}))
