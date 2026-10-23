"""Final postcontact visitor calibration, preserving all failed prototypes."""
import copy,json,pathlib
from check_semantics import receipt
from scan_rows import read_label
from row_audit_metadata import expression
HERE=pathlib.Path(__file__).resolve().parent
def main():
 original=json.loads((HERE/'MEMO-CONTROLS-v1.json').read_text())['expectations']
 results={d:receipt(f'memo-v5-depth{d}')[0] for d in (5,10,30)}
 r=results[30]
 assembled={'depth5_nodes':results[5]['nodes'],'depth30_nodes':r['nodes'],
 'right_extra_nodes':r['right_extra_nodes'],'metadata_alias_nodes':r['metadata_alias_nodes'],
 'refs_balanced':r['refs_balanced'],'refs_right_extra':r['refs_right_extra']}
 assert assembled==original
 catches=[]
 for key in assembled:
  bad=copy.deepcopy(assembled)
  if isinstance(bad[key],list):bad[key]=[]
  else:bad[key]-=1
  try:assert bad==original
  except AssertionError:catches.append(key)
  else:raise AssertionError('synthetic memo comparator blind')
 md=json.loads((HERE/'METADATA-CONTROLS-v1.json').read_text())
 rows={x['name']:x for x in read_label('memo-v5-stored-metadata')[1:] if 'record' not in x}
 p=rows[md['positive_name']]
 assert p['body']==md['positive_body'] and p['body_nodes']==2 and not p['body_refs']
 refs,n=expression(p['body']);assert not refs and n==2
 try:expression(rows[md['negative_name']]['body'])
 except ValueError:catches.append('unsupported-Syntax')
 else:raise AssertionError('unencoded Syntax accepted')
 for key in ('body_nodes','body_refs'):
  bad=copy.deepcopy(p);bad[key]=1 if key=='body_nodes' else ['Forged.reference']
  try:
   refs,n=expression(bad['body']);assert n==bad['body_nodes'] and refs==set(bad['body_refs'])
  except AssertionError:catches.append('stored-'+key)
  else:raise AssertionError('stored-body comparator blind')
 result={'status':'POSTCONTACT-VISITOR-CALIBRATED','exact_depth30_expanded_nodes':r['nodes'],
 'distinct_cached_subexpressions':r['cache_entries'],'catches':catches,
 'full_stored_metadata_positive':True,'new_blind_replication_credit':False}
 (HERE/'VISITOR-CALIBRATION-v1.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
