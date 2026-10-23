import copy,importlib.util,json,pathlib,time
P=pathlib.Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('ownaudit',P/'audit_exact_v1.py');a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
records=[];results=[];at=time.perf_counter();report={'status':'FAIL','commands':records,'controls':results,'candidate_contact':True,'scope':'postrelease instrument extension; no blind credit','script_sha256':a.sha(pathlib.Path(__file__))}
try:
 b=P/'value-controls-build';ds={}
 for n in ['CallerValueA','CallerValueB','CallerValueHostile']:
  ds[n]=a.audit([n],b,'value-v2-single-'+n,records);a.g.gate(ds[n],[n]);a.compatibility(ds[n]);results.append({'control':n+' standalone clean origin','pass':True})
 for ms in [['CallerValueA','CallerValueB'],['CallerValueA','CallerValueHostile'],['CallerValueHostile','CallerValueA']]:
  try:a.audit(ms,b,'value-v2-import-'+'+'.join(ms),records)
  except AssertionError as e:
   assert "environment already contains 'CallerValue.shared'" in str(e);results.append({'control':'+'.join(ms)+' import duplicate definition','rejected':True,'reason':str(e)})
  else:raise AssertionError('duplicate definition unexpectedly imported')
 for left,right in [('CallerValueA','CallerValueHostile'),('CallerValueHostile','CallerValueA')]:
  d=copy.deepcopy(ds[left]);r=copy.deepcopy(ds[right]['rows'][0]);l=d['rows'][0]
  for k in ['resolved_origin','resolved_kind','resolved_type','resolved_body','resolved_recursor_rules']:r[k]=l[k]
  d['rows'].append(r)
  try:a.compatibility(d)
  except ValueError as e:results.append({'control':'simulated coalescence '+left+'+'+right,'rejected':True,'reason':str(e)})
  else:raise AssertionError('nonproof value mismatch survived')
 report['status']='PASS'
finally:report['seconds']=time.perf_counter()-at;(P/'audit-controls-v2.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'status':report['status'],'controls':len(results),'seconds':report['seconds']}))
