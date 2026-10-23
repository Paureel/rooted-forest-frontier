#!/usr/bin/env python3
"""Complete fixed malformed and literal mutation checks on actual compiled values; no graph rerun."""
from pathlib import Path
from fractions import Fraction as F
import ast,copy,hashlib,json
P=Path(__file__).resolve().parent;R=P.parent/'sol-preparation-READY-v1/preparation';bank=json.loads((R/'fixtures-v1.json').read_text());refs=json.loads((R/'graph-battery-v2.json').read_text());checks=[]
def add(n,g,w=True):checks.append({'name':n,'got':g,'expected':w,'pass':g==w})
def parse(n):return [json.loads(z[len('READOUT_JSON '):])for z in (P/'logs'/n).read_text().splitlines()if z.startswith('READOUT_JSON ')][0]
m=parse('controls-ReadoutMalformed.log');f=json.loads((P/'malformed-observer-freeze-v1.json').read_text())
for k in ['missing_label_selector','duplicate_parent_selector','child_order_same_rooted_topology','suppressed_path']:add(k,m[k],f['expected_'+k])
flip=lambda a:('1'if a[0]=='0'else'0')+a[1:]if a else''
want=[sorted(flip(a)for a in h)for h in refs['fixtures'][0]['parent_source_hulls']];add('actual transported original parent hulls',m['transported_parent_hulls'],want)
# Reuse the exact pure comparator functions frozen in READY, extracting definitions without executing its top-level writer.
source=(R/'instrument/check_literal_gates.py').read_text();nodes=ast.parse(source).body;functions='\n\n'.join(ast.get_source_segment(source,n)for n in nodes if isinstance(n,ast.FunctionDef)and n.name in ['expected','gate']);env={'bank':bank,'F':F};exec(compile(functions,'READY-pure-functions','exec'),env);gate=env['gate']
rows=json.loads((P/'compiled-battery-comparison-v1.json').read_text())['observations']
for fixture in bank['fixtures']:
 r=next(z for z in rows if z['id']==fixture['id']);r=copy.deepcopy(r);r['masses']=[{'c':str(F(z['c']['num'],z['c']['den'])),'mass':str(F(z['value']['num'],z['value']['den'])),'raw_denominator':z['raw_denominator']}for z in r['masses']]
 add(fixture['id']+' unchanged READY comparator accepts actual literal list and mass',gate(fixture,r))
 for name,mut in [('omission',lambda z:z['appended_raw'].pop()),('duplication',lambda z:z['appended_raw'].append(copy.deepcopy(z['appended_raw'][0]))),('changed edge',lambda z:z.update(selector={'kind':'edge','edge':['0','01']})),('false mass',lambda z:z['masses'][0].update(mass='0')),('false denominator',lambda z:z['masses'][0].update(raw_denominator=0))]:
  bad=copy.deepcopy(r);mut(bad);add(fixture['id']+' READY comparator rejects '+name,gate(fixture,bad),False)
# Same SHA256/source-size checks used at source extraction, with a clean and a deliberately corrupted copy.
original=P/'src/BinaryEdge.lean';pin=hashlib.sha256(original.read_bytes()).hexdigest();twins=P/'source-pin-twins';twins.mkdir(exist_ok=True);(twins/'clean.lean').write_bytes(original.read_bytes());(twins/'corrupt.lean').write_bytes(original.read_bytes()+b'\naxiom source_pin_plant : False\n')
add('source pin clean twin',hashlib.sha256((twins/'clean.lean').read_bytes()).hexdigest()==pin);add('source pin corrupted twin rejected',hashlib.sha256((twins/'corrupt.lean').read_bytes()).hexdigest()==pin,False)
out={'checks':checks,'denominator':len(checks),'passed':sum(z['pass']for z in checks),'all_pass':all(z['pass']for z in checks),'ready_comparator_source_sha256':hashlib.sha256(source.encode()).hexdigest(),'pure_functions_reused':functions,'fixture_expectations_changed':False,'replication_increment':0};(P/'final-literal-malformed-pin-controls-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['checks','pure_functions_reused']},indent=2));assert out['all_pass']
