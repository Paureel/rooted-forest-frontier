from pathlib import Path
import json,re,copy
b=Path(__file__).resolve().parent;d=json.loads((b/'PROVENANCE-MAP.json').read_text());mods=d['modules']
def check(rows):
 if set(rows)!=set(mods):return False
 for n,r in rows.items():
  actual=re.findall(r'^import\s+(\w+)',(b/'isolated'/(n+'.lean')).read_text(),re.M)
  if r['imports']!=actual:return False
 return all(m in mods or m in ['Std','Lean'] for r in rows.values() for m in r['imports'])
assert check(mods);first=next(n for n,x in mods.items() if x['imports']);plants={}
for kind in ['missing','duplicate','foreign']:
 bad=copy.deepcopy(mods)
 if kind=='missing':bad[first]['imports'].pop()
 elif kind=='duplicate':bad[first]['imports'].append(bad[first]['imports'][0])
 else:bad[first]['imports'].append('UnpinnedScientificModule')
 assert not check(bad);plants[kind]='REJECT exact import/source mismatch'
out={'status':'PASS-EXACT-IMPORT-CLOSURE','scientific_modules':len(mods),'external_imports':sorted({m for r in mods.values() for m in r['imports'] if m not in mods}),'clean':'ACCEPT','plants':plants,'scope':'All scientific imports are inventoried62;only standard Std/Lean remain external. No foreign scientific module can hide an unused axiom outside the origin inventory.'}
(b/'IMPORT-CLOSURE-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
