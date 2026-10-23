#!/usr/bin/env python3
"""Post-contact zero-producer extension; unchanged prerelease Lean detector."""
import copy,hashlib,json,sys
from pathlib import Path
P=Path(__file__).resolve().parent; B=P.parent; sys.path.insert(0,str(B))
import origin_gate_v3 as old
def gate(obj,modules,imports=None,fp=None):
    hs=obj['producers']
    if len(hs)!=len(modules) or {h['module'] for h in hs}!=set(modules): raise ValueError('exact producer headers')
    for h in hs:
        if type(h['count']) is not int or h['count']<0: raise ValueError('invalid count')
        if imports is not None and h['imports']!=imports[h['module']]: raise ValueError('actual stored import changed')
        if h['count']==0 and any(r['producer']==h['module'] for r in obj['rows']): raise ValueError('fake empty producer')
    nonzero=[h['module'] for h in hs if h['count']>0]
    reduced=dict(obj); reduced['producers']=[h for h in hs if h['count']>0]
    old.gate(reduced,nonzero,None,fp)
    return True
def main():
    records=[]; controls=[]; src=P/'empty-control'; build=src/'build'
    digest=hashlib.sha256((src/'ImportOnly.lean').read_bytes()).hexdigest()
    assert digest==json.loads((P/'EMPTY-CONTROL-SHA-v1.json').read_text())['ImportOnly.lean']
    old.compile_one('ImportOnly',src,build,str(P/'empty-control-compile'),records)
    r=old.run(['--run',str(B/'origin/ProducerAudit_v1.lean'),'ImportOnly'],src,build,str(P/'empty-control-audit'),records)
    assert r.returncode==0
    empty=json.loads(r.stdout); assert empty['producers'][0]['count']==0 and empty['rows']==[]
    gate(empty,['ImportOnly'],{'ImportOnly':['Init','Init','Std']}); controls.append({'id':'actual empty producer','pass':True})
    replay=[('origin-full-CleanA-v3.json',True),('origin-full-CleanA+CleanB-v3.json',True),('origin-full-GeneratedPrivateClean-v3.json',True),('origin-full-UnusedAxiom-v3.json',False),('origin-full-PrivateAxiom-v3.json',False),('origin-full-CleanA+PrivateAxiom-v3.json',False),('origin-full-CleanA+HostileCoalesced-v3.json',False),('private-twin-clean-v3.json',True),('private-twin-both-v3.json',False)]
    for file,clean in replay:
        d=json.loads((B/file).read_text()); ms=[h['module'] for h in d['producers']]
        if clean: gate(d,ms,{m:['Init','Init','Std'] for m in ms}); controls.append({'id':file,'pass':True})
        else: old.must_reject(file,lambda:gate(d,ms,{m:['Init','Init','Std'] for m in ms}),controls)
    baseline=json.loads((B/'origin-full-CleanA-v3.json').read_text())
    missing=copy.deepcopy(baseline); missing['rows'].pop(); old.must_reject('missing nonzero row',lambda:gate(missing,['CleanA']),controls)
    dup=copy.deepcopy(baseline); dup['rows'].append(dup['rows'][0]); old.must_reject('duplicate nonzero row',lambda:gate(dup,['CleanA']),controls)
    zero=copy.deepcopy(baseline); zero['producers'][0]['count']=0; old.must_reject('fake zero count with rows',lambda:gate(zero,['CleanA']),controls)
    absent=copy.deepcopy(empty); absent['producers']=[]; old.must_reject('missing empty header',lambda:gate(absent,['ImportOnly']),controls)
    double=copy.deepcopy(empty); double['producers']*=2; old.must_reject('duplicate empty header',lambda:gate(double,['ImportOnly']),controls)
    body=copy.deepcopy(baseline); next(r for r in body['rows'] if r['body'] is not None)['body']+='CORRUPT'; old.must_reject('body receipt alteration',lambda:gate(body,['CleanA']),controls)
    for tag in ('body','import'):
        d=json.loads((B/('origin-adapt-'+tag+'-audit-v3.json')).read_text())
        old.must_reject('actual '+tag+' adaptation',lambda:gate(d,['CleanA'],{'CleanA':['Init','Init','Std']},old.fingerprint(baseline) if tag=='body' else None),controls)
    raw=json.loads((P/'candidate-audit-full-run1.json').read_text()); inv=json.loads((P/'source-inventory-v2.json').read_text()); imports={x['module']:['Init','Init']+x['imports'] for x in inv['sources']}
    gate(raw,list(imports),imports)
    result={'status':'PRODUCER_GATE_PASS','schema_extension':'post-contact zero-count producer; unchanged Lean detector','controls':controls,'commands':records,'modules':len(raw['producers']),'nonempty_producers':sum(h['count']>0 for h in raw['producers']),'stored_occurrences':len(raw['rows']),'unique_resolved_names':len({r['name'] for r in raw['rows']}),'standard_axioms':sorted({a for r in raw['rows'] for a in r['axioms']}),'direct_custom_axioms':[r['name'] for r in raw['rows'] if r['kind']=='axiom' and r['name'] not in old.ALLOW],'raw_inventory_sha256':old.sha(P/'candidate-audit-full-run1.json'),'instrument_sha256':old.sha(B/'origin/ProducerAudit_v1.lean')}
    (P/'candidate-producer-gate-v2.json').write_text(json.dumps(result,indent=2)+'\n')
    assert hashlib.sha256((src/'ImportOnly.lean').read_bytes()).hexdigest()==digest
    print(json.dumps({k:v for k,v in result.items() if k not in ('controls','commands')}))
if __name__=='__main__': main()
