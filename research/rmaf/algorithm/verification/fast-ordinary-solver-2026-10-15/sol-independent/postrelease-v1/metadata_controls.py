"""Postcontact instrument calibration against independent hand metadata values."""
import copy,json,pathlib
from scan_rows import read_label
from row_audit_metadata import expression
HERE=pathlib.Path(__file__).resolve().parent
def main():
 frozen=json.loads((HERE/'METADATA-CONTROLS-v1.json').read_text())
 rr=read_label('metadata-produced-controls');rows={r['name']:r for r in rr[1:] if 'record' not in r}
 p=rows[frozen['positive_name']];expected=frozen['positive_body']
 assert p['body']==expected,('hand positive structure',p['body'],expected)
 refs,nodes=expression(p['body']);assert refs==set(frozen['positive_body_refs']) and nodes==frozen['positive_nodes']
 assert p['body_refs']==[] and p['body_nodes']==2
 negative=rows[frozen['negative_name']]
 assert negative['body'][1][0][1][0]=='syntax-unencoded'
 try:expression(negative['body'])
 except ValueError as e:assert 'Syntax metadata unsupported' in str(e)
 else:raise AssertionError('unencoded Syntax accepted')
 catches=['unsupported-Syntax-retained-and-refused']
 for kind in frozen['corruptions']:
  bad=copy.deepcopy(p['body']);fake_refs=[]
  if kind=='missing entry':bad[1].pop()
  elif kind=='duplicate entry':bad[1].append(copy.deepcopy(bad[1][0]))
  elif kind=='wrong bool':bad[1][1][1][1]=False
  elif kind=='wrong huge Nat':bad[1][3][1][1]-=1
  elif kind=='wrong negative Int':bad[1][4][1][1]=19
  elif kind=='truncated Name':bad[1][2][1][1]=['str']
  elif kind=='unknown DataValue tag':bad[1][0][1][0]='UNKNOWN'
  elif kind=='unknown expression child':bad[2]=['UNKNOWN']
  elif kind=='forged body refs':fake_refs=['Forged.reference']
  else:raise AssertionError('unhandled mutation')
  try:
   actual,n=expression(bad)
   if bad!=expected or actual!=set(fake_refs) or n!=frozen['positive_nodes']:raise ValueError('exact hand comparator')
  except (ValueError,AssertionError):catches.append(kind)
  else:raise AssertionError('mutation escaped '+kind)
 result={'status':'POSTCONTACT-METADATA-CALIBRATION-PASS','catches':catches,
         'positive_full_body_exact':True,'primitive_types':['string','bool','Name','Nat','Int'],
         'unencoded_Syntax_still_refused':True,'new_blind_replication_credit':False}
 (HERE/'METADATA-CALIBRATION-v1.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
