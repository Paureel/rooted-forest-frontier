"""Independent hand-value controls for postcontact DAG traversal extension."""
import copy,json,pathlib
from check_semantics import receipt
from scan_rows import read_label
from row_audit_metadata import expression
HERE=pathlib.Path(__file__).resolve().parent
def main():
 frozen=json.loads((HERE/'MEMO-CONTROLS-v1.json').read_text());rr=receipt('memo-synthetic-output')
 assert len(rr)==1 and rr[0]==frozen['expectations'],('shared expression expectation',rr)
 catches=[]
 for name,key in [('wrong expanded node count','depth30_nodes'),('lost right-branch reference','refs_right_extra'),('metadata node erased','metadata_alias_nodes')]:
  bad=copy.deepcopy(rr[0]);bad[key]=[] if isinstance(bad[key],list) else bad[key]-1
  try:assert bad==frozen['expectations']
  except AssertionError:catches.append(name)
  else:raise AssertionError('memo comparator blind')
 md=json.loads((HERE/'METADATA-CONTROLS-v1.json').read_text());stored=read_label('memo-stored-metadata')
 ds={r['name']:r for r in stored[1:] if 'record' not in r};positive=ds[md['positive_name']]
 assert positive['body']==md['positive_body'] and positive['body_nodes']==2 and positive['body_refs']==[]
 refs,nodes=expression(positive['body']);assert not refs and nodes==2
 bad=copy.deepcopy(positive['body']);bad[1][0][1]=['string']
 try:expression(bad)
 except ValueError:catches.append('truncated metadata primitive')
 else:raise AssertionError('metadata corruption escaped')
 try:expression(ds[md['negative_name']]['body'])
 except ValueError:catches.append('unsupported Syntax still refused')
 else:raise AssertionError('Syntax unexpectedly accepted')
 result={'status':'POSTCONTACT-DAG-CALIBRATION-PASS','catches':catches,
 'depth30_exact_expanded_nodes':2147483647,'actual_stored_metadata_positive':True,
 'new_blind_replication_credit':False}
 (HERE/'MEMO-CALIBRATION-v1.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
