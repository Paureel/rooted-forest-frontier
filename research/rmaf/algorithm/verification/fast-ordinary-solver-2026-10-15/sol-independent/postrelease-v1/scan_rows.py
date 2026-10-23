"""Fresh complete-row collector, reusing only own frozen structural expression parser.

Known refusals are retained per declaration while unaffected flags/dependency data
are collected. This program does not treat a refused body as fully audited.
"""
import gzip,hashlib,json,pathlib,sys,time
from row_audit_frozen import expression
HERE=pathlib.Path(__file__).resolve().parent
def read_label(label):
 paths=[]
 for p in (HERE/'evidence').glob('*.json'):
  r=json.loads(p.read_text())
  if r['label']==label:paths.append(r)
 if len(paths)!=1:raise ValueError(('label denominator',label,len(paths)))
 rec=paths[0]
 if rec['returncode']!=0 or rec['stop_reason']:raise ValueError(('producer stopped',label))
 rows=[];raw=0
 for sh in rec['shards']:
  p=HERE/sh['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==sh['sha256']
  with gzip.open(p,'rb') as f:
   for line in f:
    raw+=len(line)
    if raw>64*1024**2 or len(line)>16*1024**2:raise ValueError('raw cap')
    rows.append(json.loads(line))
 assert raw==rec['raw_bytes'];assert rows[0]['count']==sum('record' not in r for r in rows[1:])
 return rows
def main():
 begun=time.perf_counter();label=sys.argv[1];rr=read_label(label);decls=[r for r in rr[1:] if 'record' not in r]
 assert len({r['name'] for r in decls})==len(decls)
 failures=[];nodes=0;proof_nodes=0;unsafe=[];partial=[];axioms=[];full_rows=0
 for r in decls:
  n=r['name']
  if r['unsafe']:unsafe.append(n)
  if r['partial']:partial.append(n)
  if r['kind']=='axiom':axioms.append(n)
  try:
   refs,count=expression(r['type']);nodes+=count
   assert refs==set(r['type_refs']), 'type refs'
   if r['kind']=='theorem':
    assert r['proof_body_omitted_after_actual_walk'] and r['body'] is None and r['body_nodes']>0
    proof_nodes+=r['body_nodes']
   elif r['kind'] in ('definition','opaque'):
    assert r['body'] is not None and not r['proof_body_omitted_after_actual_walk']
    refs,count=expression(r['body']);nodes+=count
    assert refs==set(r['body_refs']) and count==r['body_nodes'],'body refs/count'
   else:assert r['body'] is None and r['body_nodes']==0
   if r['kind']=='recursor':
    for rule in r['data_payload']['rules']:
     _,count=expression(rule['rhs']);nodes+=count
   full_rows+=1
  except (ValueError,AssertionError) as e:
   failures.append({'name':n,'module':r['module'],'kind':r['kind'],'reason':str(e)})
 result={'label':label,'declared_modules':rr[0]['modules'],'declarations':len(decls),'full_structural_rows':full_rows,
 'full_expression_nodes':nodes,'actual_proof_nodes_walked_by_pinned_producer':proof_nodes,
 'refusals':failures,'unsafe':unsafe,'partial':partial,'custom_axioms':axioms,'seconds':time.perf_counter()-begun,
 'raw_cleanliness':not(failures or unsafe or partial or axioms),'proof_or_solver_correctness':False}
 (HERE/(label+'-AUDIT-v1.json')).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ('unsafe','partial','refusals')},sort_keys=True))
 print(json.dumps({'first_refusals':failures[:3],'unsafe_count':len(unsafe),'first_unsafe':unsafe[:3],'partial_count':len(partial)},sort_keys=True))
if __name__=='__main__':main()
