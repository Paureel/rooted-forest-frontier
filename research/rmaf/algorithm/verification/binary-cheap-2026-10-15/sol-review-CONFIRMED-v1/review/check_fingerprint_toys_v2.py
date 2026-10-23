#!/usr/bin/env python3
"""Producer-origin, complete declaration, and normalized exact type/value adoption checks."""
from pathlib import Path
import copy,hashlib,json
P=Path(__file__).resolve().parent
checks=[]
def add(n,g,w=True):checks.append({'name':n,'got':g,'expected':w,'pass':g==w})
def parse(n,tag):
 a=[json.loads(z[len(tag):])for z in (P/'logs'/n).read_text().splitlines()if z.startswith(tag)]
 if len(a)!=1:raise RuntimeError('Nonunique '+n)
 return a[0]
def norm(rs):return sorted([{k:r[k]for k in ['user_name','private','kind','type','value']}for r in rs],key=lambda d:d['user_name'])
def good(rs,want):
 ns=[(d['origin'],d['name'])for d in rs]
 return bool(rs)and len(ns)==len(set(ns))and len(rs)==len(want)and norm(rs)==norm(want)
a=parse('fingerprint-controls-v2-FingerprintToyClean.log','FINGERPRINT_JSON ');b=parse('fingerprint-controls-v2-FingerprintToyTwin.log','FINGERPRINT_JSON ');bad=parse('fingerprint-controls-v2-FingerprintToyBad.log','FINGERPRINT_JSON ')
add('Std-only fingerprint clean denominator',len(a),19);add('Std-only same bodies/private/generated twin',good(b,a));add('Std-only changed body rejected',good(bad,a),False)
add('Std-only changed body retains every name and type',[{k:r[k]for k in ['user_name','private','kind','type']}for r in norm(a)],[{k:r[k]for k in ['user_name','private','kind','type']}for r in norm(bad)])
for name,z in [('empty',[]),('missing private',[d for d in a if not d['private']]),('duplicate',a+[copy.deepcopy(a[0])])]:add('fingerprint '+name+' rejects',good(z,a),False)
toy_checks=copy.deepcopy(checks)
if not all(z['pass']for z in checks):
 (P/'fingerprint-toy-v2-FAILURE.json').write_text(json.dumps({'checks':checks},indent=2)+'\n');raise SystemExit('Fingerprint toy gate failed; scientific adoption comparison not run')

out={"checks":checks,"denominator":len(checks),"all_pass":all(z["pass"]for z in checks)}
(P/"fingerprint-toy-comparison-v2.json").write_text(json.dumps(out,indent=2)+"\n")
print("Fingerprint type/value toy gates:",len(checks),"/",len(checks))
