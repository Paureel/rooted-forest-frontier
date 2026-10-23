"""Check frozen dynamic DAG pilot values; preserves an actual cache-invariant failure."""
import json,pathlib,sys
from check_semantics import receipt
HERE=pathlib.Path(__file__).resolve().parent
f=json.loads((HERE/'MEMO-DYNAMIC-PILOT-v1.json').read_text());label=sys.argv[1];d=int(sys.argv[2])
rows=receipt(label);assert len(rows)==1;r=rows[0]
expected={'depth':d,'nodes':f[f'depth{d}_nodes'],'cache_entries':f['expected_distinct_subexpressions'][str(d)],
          'right_extra_nodes':f[f'depth{d}_nodes']+2,'metadata_alias_nodes':4,
          'refs_balanced':['Synthetic.A'],'refs_right_extra':['Synthetic.A','Synthetic.B']}
assert r==expected,{'actual':r,'expected':expected}
print(json.dumps({'status':'EXACT-SYNTHETIC-DAG-PILOT-PASS','label':label,'depth':d,'expanded_nodes':r['nodes'],'cache_entries':r['cache_entries']}))
