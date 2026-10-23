#!/usr/bin/env python3
"""One-shot measured isolated toy gate; scientific candidate compilation forbidden."""
import argparse,copy,hashlib,json,os,re,subprocess,time
from pathlib import Path
P=Path(__file__).resolve().parent.parent;S=P/'toy-src';B=P/'toy-build';L=P/'logs'
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
POL=json.loads((P/'toy-policy-v1.json').read_text());ALLOW=set(POL['standard_axiom_allowlist'])
def allowed(txt):
 imps=re.findall(r'^import\s+(\S+)\s*$',txt,re.M)
 return bool(imps) and all(m in POL['allowed_imports'] for m in imps)
def compile_one(n,stage,audit=False):
 path=S/(n+'.lean')
 if not allowed(path.read_text()):raise RuntimeError('Unapproved import '+n)
 env=os.environ.copy();env['LEAN_PATH']=str(B);cmd=[str(LEAN),'-o',str(B/(n+'.olean')),n+'.lean'];st=time.perf_counter()
 p=subprocess.run(cmd,cwd=S,env=env,text=True,capture_output=True,timeout=55);secs=time.perf_counter()-st
 log=L/(stage+'-'+n+'.log');log.write_text(p.stdout+p.stderr)
 row={'module':n,'command':cmd,'LEAN_PATH':str(B),'seconds':secs,'exit_code':p.returncode,'log':str(log.relative_to(P)),
      'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
 if p.returncode:raise RuntimeError('Toy compilation failed '+n)
 row['binary_sha256']=hashlib.sha256((B/(n+'.olean')).read_bytes()).hexdigest()
 if audit:
  rs=[json.loads(z[len('AUDIT_JSON '):]) for z in p.stdout.splitlines() if z.startswith('AUDIT_JSON ')]
  if len(rs)!=1:raise RuntimeError('Nonunique audit receipt '+n)
  row['audit']=rs[0]
 return row
def accept(a,origins,expected=None):
 ds=a['declarations'];names=[(d['origin'],d['name']) for d in ds]
 return bool(ds) and a['count']==len(ds) and len(names)==len(set(names)) and set(a['requested_origins'])==set(origins) and set(d['origin'] for d in ds)==set(origins) and (expected is None or ds==expected) and all((d['kind']!='axiom' or d['name'] in ALLOW) and set(d['axioms'])<=ALLOW for d in ds)
def checkrows(rows):
 checks=[]
 def add(n,g,w=True):checks.append({'name':n,'got':g,'expected':w,'pass':g==w})
 source={r['module']:r['audit'] for r in rows if 'audit'in r and not r['module'].startswith('Import')}
 for n in POL['modules']:
  a=source[n];b=next(r['audit'] for r in rows if r['module']=='Import'+n)
  add(n+' all-origin axiom verdict',accept(a,[n]),POL['expected_accept'][n]);add(n+' complete source/import inventory',a['declarations'],b['declarations'])
  add(n+' all origins actual',set(d['origin'] for d in a['declarations'])=={n})
 clean=source['ToyClean'];ds=clean['declarations'];add('clean exact denominator',len(ds),POL['expected_clean_declarations'])
 add('private clean declaration retained',any(d['private'] and d['user_name']=='ToyClean.hidden' for d in ds))
 add('generated recursor retained',any(d['name']=='ToyClean.Packet.rec' and d['kind']=='recursor' for d in ds))
 u=source['ToyUnused'];add('unused outside namespace retained',any(d['name']=='outside_namespace_unused' and d['kind']=='axiom' for d in u['declarations']))
 add('harmless public theorem closure misses unused axiom',next(d['axioms'] for d in u['declarations'] if d['name']=='ToyUnused.harmless'),[])
 prefix=copy.deepcopy(u);prefix['declarations']=[d for d in u['declarations'] if d['name'].startswith('ToyUnused.')];prefix['count']=len(prefix['declarations']);add('namespace-prefix audit false acceptance',accept(prefix,['ToyUnused']))
 add('private axiom detected',any(d['private'] and d['kind']=='axiom' for d in source['ToyPrivate']['declarations']))
 add('foreign unused origin reachable through consumer closure',any('ToyExternal.importedBad'in d['axioms'] for d in source['ToyUseExternal']['declarations']))
 for n,mut in [('zero inventory',lambda a:a.update(declarations=[],count=0)),('missing origin',lambda a:a.update(requested_origins=['Missing'])),
               ('missing private declaration',lambda a:a.update(declarations=[d for d in a['declarations'] if not d['private']],count=sum(not d['private'] for d in a['declarations']))),
               ('duplicate origin row',lambda a:(a['declarations'].append(copy.deepcopy(a['declarations'][0])),a.update(count=a['count']+1)))]:
  a=copy.deepcopy(clean);mut(a);add(n+' rejected',accept(a,['ToyClean'],ds),False)
 body=(S/'ToySource.body').read_text()
 for old,new in POL['expected_adapter']:body=body.replace(old,new)
 add('exact import/type adapter accepted',(S/'ToyAdapted.body').read_text()==body)
 add('changed body adapter rejected',(S/'ToyTampered.body').read_text()==body,False)
 norm=lambda n:sorted((d['user_name'],d['private'],d['kind']) for d in source[n]['declarations'])
 add('complete private/generated adoption fingerprint',norm('ToySource'),norm('ToyAdapted'))
 add('changed body has same adoption names',norm('ToyAdapted'),norm('ToyTampered'))
 add('unapproved scientific import refused before compile',allowed('import RMAF\n'),False)
 return checks
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('stage',choices=['pilot','battery']);a=ap.parse_args();st=time.perf_counter();rows=[]
 try:
  if a.stage=='pilot':
   rows.append(compile_one('OriginAudit','pilot'));rows.append(compile_one('ToyClean','pilot',True));rows.append(compile_one('ImportToyClean','pilot',True))
   checks=[{'name':'clean all-origin verdict','pass':accept(rows[1]['audit'],['ToyClean'])},{'name':'clean source/import exact full inventory','pass':rows[1]['audit']==rows[2]['audit']}]
  else:
   p=json.loads((P/'toy-pilot-v1.json').read_text())
   if not p['all_pass']:raise RuntimeError('pilot prerequisite failed')
   rows=p['executions'][:]
   for n in POL['modules'][1:]:
    rows.append(compile_one(n,'battery',True));rows.append(compile_one('Import'+n,'battery',True))
   checks=checkrows(rows)
  out={'phase':'PRE-CANDIDATE ONLY','stage':a.stage,'executions':rows,'checks':checks,'denominator':len(checks),'passed':sum(z['pass'] for z in checks),'all_pass':all(z['pass'] for z in checks),
       'seconds':time.perf_counter()-st,'candidate_compilation':False,'replication_increment':0}
  (P/('toy-'+a.stage+'-v1.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['executions','checks']},indent=2));raise SystemExit(0 if out['all_pass'] else 1)
 except Exception as ex:
  (P/('toy-'+a.stage+'-v1-FAILURE.json')).write_text(json.dumps({'failure':repr(ex),'completed_executions':rows,'seconds':time.perf_counter()-st},indent=2)+'\n');raise
