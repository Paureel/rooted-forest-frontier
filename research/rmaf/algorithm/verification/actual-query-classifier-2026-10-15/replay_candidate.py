from pathlib import Path
import os,json,re,subprocess,time,hashlib,datetime
b=Path(__file__).resolve().parent;root=b.parents[4]
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allresults={}
for label,false in [('query','FalsePrecontrols'),('rank','FalseProbe')]:
 iso=b/('isolated-'+label);logs=b/('logs-'+label);logs.mkdir(exist_ok=True)
 pinned=json.loads((b/'CANDIDATE-PIN.json').read_text())['packages'][label]['copied_sources']
 sources={x['module']:iso/(x['module']+'.lean') for x in pinned if x['module']!=false}
 for x in pinned:assert h(iso/(x['module']+'.lean'))==x['sha256'],x
 deps={n:[m for m in re.findall(r'^import\s+(\w+)',p.read_text(),re.M) if m in sources] for n,p in sources.items()}
 order=[]
 def visit(n):
  if n in order:return
  for m in deps[n]:visit(m)
  order.append(n)
 for n in sources:visit(n)
 env=os.environ.copy();env['LEAN_PATH']=str(iso)
 rows=[]
 def build(n,positive=True):
  t=time.monotonic();r=subprocess.run([str(root/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
  log=logs/(n+'.log');log.write_text(r.stdout)
  row={'module':n,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':h(iso/(n+'.lean')),'log_sha256':h(log)};rows.append(row)
  if positive:assert r.returncode==0,(label,n,r.stdout)
  return r
 for n in order:build(n)
 template=(b/'std-toys/ToyAudit.lean').read_text()
 imports='\n'.join('import '+n for n in order)
 template=template.replace('import ToyClean\nimport ToyUsed\nimport ToyUnused',imports).replace('["ToyClean","ToyUsed","ToyUnused"]',json.dumps(order)).replace('TOY_ORIGIN ','REVIEW_ORIGIN ')
 (iso/'IndependentAudit.lean').write_text(template)
 r=build('IndependentAudit');audit=[json.loads(l.split('REVIEW_ORIGIN ',1)[1]) for l in r.stdout.splitlines() if 'REVIEW_ORIGIN ' in l]
 assert set(x['origin'] for x in audit)==set(order)
 assert len(audit)==len({x['name'] for x in audit})
 allowed={'Classical.choice','Quot.sound','propext'}
 assert all(x['kind']!='axiom' and set(x['axioms'])<=allowed for x in audit)
 fr=build(false,False)
 count=fr.stdout.count('Tactic `decide` proved that the proposition')
 assert fr.returncode!=0 and count==(4 if label=='query' else 3),fr.stdout
 allresults[label]={'positive_order':order,'source_builds':len(order),'builds':rows,'origins':audit,'declarations':len(audit),'private':sum('_private.' in x['name'] for x in audit),'module_counts':{n:sum(x['origin']==n for x in audit) for n in order},'axiom_union':sorted({a for x in audit for a in x['axioms']}),'explicit_false_diagnostics':count}
 (b/('REPLAY-'+label.upper()+'.json')).write_text(json.dumps(allresults[label],indent=2)+'\n')
 print(json.dumps({'label':label,**{k:v for k,v in allresults[label].items() if k not in ['origins','builds','positive_order','module_counts']}}),flush=True)
(b/'REPLAY-SUMMARY.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_only':True,'packages':{k:{a:c for a,c in v.items() if a not in ['origins','builds']} for k,v in allresults.items()}},indent=2)+'\n')
