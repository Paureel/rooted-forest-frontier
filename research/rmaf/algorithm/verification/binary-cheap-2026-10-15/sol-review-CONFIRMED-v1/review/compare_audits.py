#!/usr/bin/env python3
"""All actual originating declarations, including private/generated/unused custom axioms."""
from pathlib import Path
import argparse,copy,hashlib,json
P=Path(__file__).resolve().parent;R=P.parent/'sol-preparation-READY-v1/preparation';ALLOW={'propext','Quot.sound','Classical.choice'}
def parse(n):
 rs=[json.loads(z[len('AUDIT_JSON '):])for z in (P/'logs'/n).read_text().splitlines()if z.startswith('AUDIT_JSON ')]
 if len(rs)!=1:raise RuntimeError('Nonunique audit '+n)
 return rs[0]
def accept(a,wanted,expected=None):
 ds=a['declarations'];ns=[(d['origin'],d['name'])for d in ds]
 return bool(ds)and a['count']==len(ds)and set(a['requested_origins'])==set(wanted)and set(d['origin']for d in ds)==set(wanted)and len(ns)==len(set(ns))and (expected is None or ds==expected)and all((d['kind']!='axiom'or d['name']in ALLOW)and set(d['axioms'])<=ALLOW for d in ds)
def add(c,n,g,w=True):c.append({'name':n,'got':g,'expected':w,'pass':g==w})
ap=argparse.ArgumentParser();ap.add_argument('stage',choices=['pilot','planted','scientific']);arg=ap.parse_args();checks=[]
if arg.stage=='pilot':
 a=parse('audit-pilot-ToyClean.log');b=parse('audit-pilot-AuditClean.log');add(checks,'clean all-origin accepts',accept(a,['ToyClean']));add(checks,'clean complete source/import equality',a['declarations'],b['declarations']);add(checks,'clean exact full denominator',a['count'],19);inventory=b
elif arg.stage=='planted':
 a=parse('audit-controls-AuditPlanted.log');inventory=a
 old=json.loads((R/'toy-battery-v1.json').read_text())['executions'];wanted=['ToyClean','ToyUnused','ToyPrivate','ToyUseExternal']
 add(checks,'all four actual origins retained',set(d['origin']for d in a['declarations'])==set(wanted))
 for name in wanted:
  ds=[d for d in a['declarations']if d['origin']==name];frozen=next(z['audit']['declarations']for z in old if z['module']==name);add(checks,name+' frozen source/import full inventory',ds,frozen)
  one={'requested_origins':[name],'declarations':ds,'count':len(ds)};add(checks,name+' expected standard-axiom verdict',accept(one,[name]),name=='ToyClean')
 add(checks,'unused outside-namespace axiom retained',any(d['name']=='outside_namespace_unused'and d['kind']=='axiom'for d in a['declarations']))
 add(checks,'private custom axiom retained',any(d['origin']=='ToyPrivate'and d['kind']=='axiom'and d['private']for d in a['declarations']))
 add(checks,'foreign custom axiom closure reached',any(d['origin']=='ToyUseExternal'and'ToyExternal.importedBad'in d['axioms']for d in a['declarations']))
 clean=parse('audit-pilot-AuditClean.log');ds=clean['declarations']
 for name,mut in [('missing actual origin',lambda b:b.update(requested_origins=['Missing'])),('missing private declaration',lambda b:b.update(declarations=[d for d in ds if not d['private']],count=sum(not d['private']for d in ds))),('duplicate actual declaration',lambda b:(b['declarations'].append(copy.deepcopy(ds[0])),b.update(count=b['count']+1)))]:
  b=copy.deepcopy(clean);mut(b);add(checks,name+' rejects',accept(b,['ToyClean'],ds),False)
else:
 if not json.loads((P/'audit-planted-comparison-v1.json').read_text())['all_pass']:raise RuntimeError('Planted audit prerequisite failed')
 a=parse('audit-scientific-AuditScientific.log');inventory=a;wanted=json.loads((P/'source-integrity-v1.json').read_text())['positive_order'];receipt=json.loads((P/'canonical-author-certificate.json').read_text())
 add(checks,'every actual released origin and standard-axiom gate',accept(a,wanted));add(checks,'all102 origins inventoried',len(set(d['origin']for d in a['declarations'])),102);add(checks,'entire declaration denominator agrees with producer',a['count'],receipt['module_origin_declarations'])
 counts={n:sum(d['origin']==n for d in a['declarations'])for n in wanted};add(checks,'every producer module declaration denominator',counts,receipt['module_counts'])
 add(checks,'private declarations present',any(d['private']for d in a['declarations']));add(checks,'generated recursors present',any(d['kind']=='recursor'for d in a['declarations']))
out={'stage':arg.stage,'checks':checks,'denominator':len(checks),'passed':sum(z['pass']for z in checks),'all_pass':all(z['pass']for z in checks),'inventory':inventory,'origin_count':len(set(d['origin']for d in inventory['declarations'])),'private_declarations':sum(d['private']for d in inventory['declarations']),'standard_axiom_allowlist':sorted(ALLOW),'auditor_lineage':'Own unchanged READY grouped all-origin source; no author auditor/evaluator used','replication_increment':0}
(P/('audit-'+arg.stage+'-comparison-v1.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['checks','inventory']},indent=2));print('Failed:',[z['name']for z in checks if not z['pass']]);assert out['all_pass']
