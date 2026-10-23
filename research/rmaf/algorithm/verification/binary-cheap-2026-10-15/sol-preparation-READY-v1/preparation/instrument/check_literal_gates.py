#!/usr/bin/env python3
"""One-shot fixed receipt mutation gates. Replays no graph generator or candidate.

Exact output/list/cost/mass comparator prepared for later released readouts.
Uses only already frozen literal fixture expectations and retained receipts.
"""
import copy,hashlib,json
from fractions import Fraction as F
from pathlib import Path
P=Path(__file__).resolve().parent.parent
bank=json.loads((P/'fixtures-v1.json').read_text());results=json.loads((P/'graph-battery-v2.json').read_text())
def expected(f):
 if f['cheap']:
  own=[{'partition':f['cheap_partition'],'sourceCuts':f['cheap_cuts']}]
  other=[{'partition':p,'sourceCuts':c}for p,c in zip(f['opposite_partitions'],f['opposite_cuts'])]
  return {'A':own,'B':other} if f['cheap']=='A' else {'A':other,'B':own}
 return {name:[{'partition':p,'sourceCuts':c}for p,c in zip(f['raw_partitions'][name],f['raw_cuts'][name])]for name in ['A','B']}
def gate(f,r):
 e=expected(f);raw=e['A']+e['B']
 if r['selector']!={'kind':'edge','edge':[f['edge'][:-1],f['edge']]}:return False
 if any(r['calls'][name]['outputs']!=e[name]for name in ['A','B']):return False
 if r['appended_raw']!=r['calls']['A']['outputs']+r['calls']['B']['outputs'] or r['appended_raw']!=raw:return False
 if len(r['masses'])!=len(bank['rational_c']):return False
 for m,cp in zip(r['masses'],bank['rational_c']):
  c=F(*cp);v=sum((c**-len(z['sourceCuts'])for z in raw),F())
  if m!={'c':str(c),'mass':str(v),'raw_denominator':len(raw)}:return False
 return True
checks=[]
def add(n,g,w=True):checks.append({'name':n,'got':g,'expected':w,'pass':g==w})
for f,r in zip(bank['fixtures'],results['fixtures']):
 add(f['id']+' clean complete raw comparator',gate(f,r))
 for name,mut in [
  ('omitted appended occurrence',lambda z:z['appended_raw'].pop()),
  ('duplicated appended occurrence',lambda z:z['appended_raw'].append(copy.deepcopy(z['appended_raw'][0]))),
  ('different selected edge',lambda z:z.update(selector={'kind':'edge','edge':['0','01']})),
  ('false raw denominator',lambda z:z['masses'][0].update(raw_denominator=z['masses'][0]['raw_denominator']-1)),
  ('false exact mass',lambda z:z['masses'][0].update(mass='0')),
  ('omitted call output',lambda z:z['calls']['A']['outputs'].pop()),
  ('duplicated call output',lambda z:z['calls']['B']['outputs'].append(copy.deepcopy(z['calls']['B']['outputs'][0]))),
  ('wrong original source cut cost',lambda z:z['calls']['A']['outputs'][0]['sourceCuts'].pop())]:
  z=copy.deepcopy(r);mut(z);add(f['id']+' rejects '+name,gate(f,z),False)
 # Child order/address control uses a literal root-child transport, not a new input search.
 if f['cheap']:
  translate=lambda a:('1' if a[0]=='0' else '0')+a[1:]
  cuts=f['cheap_cuts'];translated=[translate(a)for a in cuts]
  add(f['id']+' root-child transport literal cut addresses',translated,
      ['11','10','1000'] if 'local'in f else ['11','101','100'])
 # Repeated occurrences must be counted even when their entire values coincide.
 o=copy.deepcopy(r['appended_raw'][0]);twins=[o,copy.deepcopy(o)];d=len(o['sourceCuts'])
 literal=sum((F(2)**-len(z['sourceCuts'])for z in twins),F());deduplicated=F(2)**-d
 add(f['id']+' legitimate repeated twin mass',literal,2*F(2)**-d)
 add(f['id']+' deduplicating legitimate twins rejected',literal==deduplicated,False)
out={'phase':'PRE-CANDIDATE ONLY','checks':checks,'denominator':len(checks),'passed':sum(z['pass']for z in checks),'all_pass':all(z['pass']for z in checks),
 'fixtures_sha256':hashlib.sha256((P/'fixtures-v1.json').read_bytes()).hexdigest(),'input_receipt_sha256':hashlib.sha256((P/'graph-battery-v2.json').read_bytes()).hexdigest(),
 'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'candidate_contact':False,'candidate_compilation':False,'replication_increment':0}
(P/'literal-mutation-results-v1.json').write_text(json.dumps(out,indent=2,default=str)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='checks'},indent=2));raise SystemExit(0 if out['all_pass'] else 1)
