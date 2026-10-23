#!/usr/bin/env python3
"""Every stored producer occurrence, without collapsing equal names across modules."""
from pathlib import Path
import argparse,copy,json
P=Path(__file__).resolve().parent;ALLOW={'propext','Classical.choice','Quot.sound'}
def parse(path,tag):
 a=[json.loads(z[len(tag):])for z in path.read_text().splitlines()if z.startswith(tag)]
 if len(a)!=1:raise RuntimeError('Nonunique '+str(path))
 return a[0]
def accept(ds):return bool(ds)and len([d['name']for d in ds])==len(set(d['name']for d in ds))and all((d['kind']!='axiom'or d['name']in ALLOW)and set(d['axioms'])<=ALLOW for d in ds)
def complete(a,wanted):
 ds=a['declarations'];pairs=[(d['origin'],d['name'])for d in ds];md={m['origin']:m for m in a['modules']}
 return bool(ds)and a['count']==len(ds)and set(md)==set(wanted)and len(pairs)==len(set(pairs))and all(m['count']==len(m['stored_names'])and m['count']==sum(d['origin']==n for d in ds)and set(m['stored_names'])==set(d['name']for d in ds if d['origin']==n)for n,m in md.items())
def add(c,n,g,w=True):c.append({'name':n,'got':g,'expected':w,'pass':g==w})
ap=argparse.ArgumentParser();ap.add_argument('stage',choices=['controls','scientific']);ar=ap.parse_args();checks=[]
if ar.stage=='controls':
 log=P/'logs/producer-data-controls-v2-AuditProducerDataControls.log';a=parse(log,'PRODUCER_DATA_JSON ');legacy=parse(log,'AUDIT_JSON ');pol=json.loads((P/'module-data-audit-freeze-v1.json').read_text())['expected_controls'];wanted=list(pol)
 add(checks,'all stored module/name pairs complete',complete(a,wanted))
 for n,e in pol.items():
  ds=[d for d in a['declarations']if d['origin']==n];add(checks,n+' producer denominator',len(ds),e['count']);add(checks,n+' complete producer axiom verdict',accept(ds),e['accept'])
 add(checks,'repeated theorem names retained per producer',sum(d['origin']in ['ProducerToyA','ProducerToyB']for d in a['declarations']),4)
 bad=[d for d in legacy['declarations']if d['origin']=='ProducerToyBad'];add(checks,'merged-origin-only rule falsely accepts coalesced custom-axiom module',accept(bad))
 add(checks,'coalesced direct custom axiom explicitly caught',any(d['origin']=='ProducerToyBad'and d['name']=='ProducerToy.ordinary'and d['kind']=='axiom'and'ProducerToy.ordinary'in d['axioms']and d['resolved_origin']=='ProducerToyA'for d in a['declarations']))
 for name,mut in [('missing module',lambda b:b.update(modules=[m for m in b['modules']if m['origin']!='ProducerToyB'])),('omitted occurrence',lambda b:(b['declarations'].pop(),b.update(count=b['count']-1))),('duplicated occurrence',lambda b:(b['declarations'].append(copy.deepcopy(b['declarations'][0])),b.update(count=b['count']+1)))]:
  b=copy.deepcopy(a);mut(b);add(checks,name+' rejects',complete(b,wanted),False)
else:
 if not json.loads((P/'producer-data-controls-comparison-v1.json').read_text())['all_pass']:raise RuntimeError('Controls not passed')
 a=parse(P/'logs/producer-data-scientific-AuditEveryProducer.log','PRODUCER_DATA_JSON ');wanted=json.loads((P/'source-integrity-v1.json').read_text())['positive_order'];add(checks,'all102 producer module/name arrays complete',complete(a,wanted));add(checks,'all102 producer modules present',len(a['modules']),102)
 for m in a['modules']:add(checks,m['origin']+' every own CI and axiom closure',accept([d for d in a['declarations']if d['origin']==m['origin']]))
 from collections import defaultdict
 byname=defaultdict(list)
 for d in a['declarations']:byname[d['name']].append(d['origin'])
 a['coalesced_name_groups']=[{'name':n,'producer_origins':ms}for n,ms in sorted(byname.items())if len(ms)>1]
 a['distinct_names']=len(byname);a['extra_producer_occurrences']=len(a['declarations'])-len(byname)
out={'stage':ar.stage,'checks':checks,'denominator':len(checks),'passed':sum(z['pass']for z in checks),'all_pass':all(z['pass']for z in checks),'inventory':a,'producer_occurrences':a['count'],'module_count':len(a['modules']),'private_occurrences':sum(d['private']for d in a['declarations']),'direct_custom_axioms':[{'origin':d['origin'],'name':d['name']}for d in a['declarations']if d['kind']=='axiom'and d['name']not in ALLOW],'replication_increment':0}
(P/('producer-data-'+ar.stage+'-comparison-v1.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['checks','inventory']},indent=2));print('Failed:',[z['name']for z in checks if not z['pass']]);assert out['all_pass']
