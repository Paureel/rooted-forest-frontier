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
 (P/'producer-fingerprint-v4-FAILURE.json').write_text(json.dumps({'checks':checks},indent=2)+'\n');raise SystemExit('Fingerprint toy gate failed; scientific adoption comparison not run')
canonical=parse('metadata-v2-FingerprintCanonical.log','FINGERPRINT_JSON ');producer=parse('producer-v2-FingerprintProducer.log','FINGERPRINT_JSON ')
add('canonical exact originating modules',sorted(set(d['origin']for d in canonical)),['DepthRestriction','Embedding']);add('original producer exact originating modules',sorted(set(d['origin']for d in producer)),['Embedding','Restriction']);raw=json.loads((P/'producer-data-scientific-comparison-v1.json').read_text())['inventory']; expected_total=sum(m['count'] for m in raw['modules'] if m['origin'] in ['DepthRestriction','Embedding']); add('canonical fingerprint covers full stored producer arrays',len(canonical),expected_total);add('original producer fingerprint denominator matches complete canonical arrays',len(producer),expected_total)
add('every normalized type/body/private/generated fingerprint equal',good(producer,canonical))
prod_audit=parse('producer-AuditProducer.log','AUDIT_JSON ');canon_audit=json.loads((P/'producer-data-scientific-comparison-v1.json').read_text())['inventory']
for origin,new in [('Restriction','DepthRestriction'),('Embedding','Embedding')]:
 old=[d for d in prod_audit['declarations']if d['origin']==origin];newrows=[d for d in canon_audit['declarations']if d['origin']==new]
 ns=lambda ds:sorted([{k:d[k]for k in ['user_name','private','kind','axioms']}for d in ds],key=lambda z:z['user_name'])
 add(origin+' exact all-origin adoption inventory',ns(old),ns(newrows));add(origin+' nonempty full denominator',len(old),len(newrows))
meta=[]
for d in canonical:
 entry={k:d[k]for k in ['origin','name','user_name','private','kind']};entry['type_sha256']=hashlib.sha256(d['type'].encode()).hexdigest();entry['value_sha256']=None if d['value']is None else hashlib.sha256(d['value'].encode()).hexdigest();meta.append(entry)
out={'checks':checks,'denominator':len(checks),'passed':sum(z['pass']for z in checks),'all_pass':all(z['pass']for z in checks),'toy_control_denominator':len(toy_checks),'canonical_origin_count':len(canonical),'producer_origin_count':len(producer),'canonical_private':sum(d['private']for d in canonical),'canonical_declaration_fingerprints':meta,'expression_normalization':'Registered v2: alpha-normalize binder names; private constant/projection names through Lean.privateToUserName?; preserve all other type/body content','timing_boundary':'Additional Expr metadata collected before its dedicated toy twins; comparisons only after twins pass. Primary exact-byte adapter/false-body gate was frozen and executed in READY. Metadata is supplemental, not an extra independent route.','replication_increment':0}
(P/'producer-adoption-comparison-v4.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['checks','canonical_declaration_fingerprints']},indent=2));print('Failed:',[z['name']for z in checks if not z['pass']]);assert out['all_pass']
