#!/usr/bin/env python3
"""Index actual stored records and inspect exact main-theorem binder chains."""
from collections import defaultdict
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
receipt=json.loads((HERE/'candidate-origin-batches-v2.json').read_text())
assert receipt['passed']
sha=lambda x:hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
index=[];by_name=defaultdict(list);signature_data={}
targets={'GenericForest.exact_of_ordinary','GenericForest.solve_sound',
         'GenericForest.source_work_bound','GenericForest.solve','GenericForest.sourceWork'}
for batch in receipt['batches']:
    data=json.loads((HERE/batch['path']).read_text())
    for r in data['occurrences']:
        a=r['actual'];row={'producer':r['producer'],'ordinal':r['ordinal'],'name':r['name'],'kind':a['kind'],
            'type_sha256':sha(a['type']),'body_sha256':sha(a['body']),'extra_sha256':sha(a['extra']),
            'direct_dependencies':a['dependencies'],'directAX_actual_all_producers':r['directAX_any_stored_producer'],
            'resolved_origin':r['resolved_origin'],'record_file':batch['path']}
        index.append(row);by_name[row['name']].append(row)
        if r['name'] in targets:
            dag=a['type'];nodes=dag['nodes'];root=dag['root'];binders=[]
            while nodes[root][0]=='forallE':
                x=nodes[root];binders.append({'name':x[1],'binder_info':x[4],'domain_root':x[2]});root=x[3]
            signature_data[r['name']]={'producer':r['producer'],'universe_parameters':a['universe_parameters'],
                'exact_type':dag,'binders':binders,'result_root':root,'kind':a['kind'],
                'unsafe':a['unsafe'],'partial':a['partial']}
assert len(index)==4977 and len(by_name)==4938
closures={}
for root in sorted(targets):
    seen=set();todo=[root];outside=set()
    while todo:
        n=todo.pop()
        if n in seen:continue
        seen.add(n)
        if n not in by_name:outside.add(n);continue
        for row in by_name[n]:todo.extend(row['direct_dependencies'])
    scientific=sorted(n for n in seen if n in by_name)
    closures[root]={'scientific_names':scientific,'external_standard_names':sorted(outside),
      'includes_ordinaryIH':'GenericForest.OrdinaryIH' in scientific,
      'includes_disjointExact':'GenericForest.DisjointExact' in scientific,
      'includes_fixture_table':'GenericForest.Controls.table' in scientific,
      'scope':'union of every stored scientific dependency occurrence; includes proof/termination dependencies, not a compiled call count'}
assert [b['name'] for b in signature_data['GenericForest.exact_of_ordinary']['binders']]==['`ordinary','`ho']
assert all(b['binder_info']=='Lean.BinderInfo.default' for b in signature_data['GenericForest.exact_of_ordinary']['binders'])
assert not signature_data['GenericForest.exact_of_ordinary']['universe_parameters']
assert not closures['GenericForest.solve']['includes_fixture_table']
assert not closures['GenericForest.solve']['includes_ordinaryIH']
assert not closures['GenericForest.solve']['includes_disjointExact']
(HERE/'DECLARATION-INDEX-v1.json').write_text(json.dumps(index,indent=2)+'\n')
(HERE/'SIGNATURES-AND-CLOSURES-v1.json').write_text(json.dumps({'signatures':signature_data,'closures':closures},indent=2)+'\n')
print(json.dumps({'stored':len(index),'unique':len(by_name),'exactness_binders':signature_data['GenericForest.exact_of_ordinary']['binders'],
 'solve_scientific_dependency_names':len(closures['GenericForest.solve']['scientific_names']),
 'solve_fixture_table_dependency':closures['GenericForest.solve']['includes_fixture_table']}))
