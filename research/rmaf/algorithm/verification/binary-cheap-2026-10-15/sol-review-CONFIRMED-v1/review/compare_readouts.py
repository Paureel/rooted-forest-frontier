#!/usr/bin/env python3
"""Actual compiled readouts vs unchanged READY literal values and original graph certificates."""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,importlib.util,json
P=Path(__file__).resolve().parent;READY=P.parent/'sol-preparation-READY-v1/preparation';bank=json.loads((READY/'fixtures-v1.json').read_text());ref=json.loads((READY/'graph-battery-v2.json').read_text())
sp=importlib.util.spec_from_file_location('own_original_graph',READY/'instrument/x0_evaluator_reused.py');x=importlib.util.module_from_spec(sp);sp.loader.exec_module(x)
def parse(n):return [json.loads(z[len('READOUT_JSON '):])for z in (P/'logs'/n).read_text().splitlines()if z.startswith('READOUT_JSON ')]
def add(checks,n,g,w=True):checks.append({'name':n,'got':g,'expected':w,'pass':g==w})
def expected_outputs(f,name):
 if f['cheap']:
  own=[{'partition':f['cheap_partition'],'sourceCuts':f['cheap_cuts']}];other=[{'partition':p,'sourceCuts':c}for p,c in zip(f['opposite_partitions'],f['opposite_cuts'])]
  return own if name==f['cheap']else other
 return [{'partition':p,'sourceCuts':c}for p,c in zip(f['raw_partitions'][name],f['raw_cuts'][name])]
def local_compare(f,got,checks,label):
 want=f['local'];add(checks,label+' exact local source',got['S'],want['S']);add(checks,label+' exact local target',got['T'],want['T']);r=got['result'];add(checks,label+' actual pretest found',r['kind'],'found')
 if r['kind']!='found':return
 add(checks,label+' global-minimum frozen cost',r['cost'],want['minimum']);add(checks,label+' literal first local certificate',r['cuts'],want['own_first_certificate']);add(checks,label+' compiled local agreement',r['agreement'])
 s,t=x.Graph(got['S']),x.Graph(got['T']);cp=s.cut_parts(r['cuts']);add(checks,label+' literal original LOCAL cut realization',cp is not None and cp['parts']==x.canon(r['partition']) and not cp['empty_components']and cp['graph_components']==len(r['cuts'])+1)
 add(checks,label+' independent local agreement',x.agreement(s,t,s.labels,r['partition']))
 add(checks,label+' certificate belongs frozen valid local edges',all(e in want['all_valid_one_edges']for e in r['cuts']))
 qcp=s.cut_parts(want['capped_cost2_certificate']);add(checks,label+' min1 does not discount capped2 legal answer',x.agreement(s,t,s.labels,qcp['parts'])and len(qcp['parts'])-1==2 and r['cost']==1)
 whole=x.Graph(f['S']).cut_parts(r['cuts']);parent=f['P'][0 if f['cheap']=='A'else 1];proj=[set(z)&set(parent)for z in whole['parts']if set(z)&set(parent)]
 add(checks,label+' local address is not whole-original reconstruction',x.canon(proj)!=cp['parts'])
def evaluate(f,r,old,checks):
 prefix=f['id']+' / ';a=lambda n,g,w=True:add(checks,prefix+n,g,w)
 a('exact original S',r['S'],f['S']);a('exact original T',r['T'],f['T']);a('literal selector',r['selector'],{'kind':'edge','edge':[f['edge'][:-1],f['edge']]});a('same selected edge under swap',r['selector_swap'],r['selector'])
 for k in ['source_nodup','target_nodup','same_labels','partition_P','source_P','C_good','C_clear']:a('actual premise '+k,r[k])
 a('actual bad A/B',[r['A_good'],r['B_good']],[False,False]);a('literal sectors',[sorted(z)for z in r['sectors']],f['expected_sectors']);a('actual sector goodness',r['sector_good'],f['expected_sector_good']);a('derived actual rank4',r['rank'],[4,4]);a('literal q3 probes',r['probe'],[bool(f['expected_probe']['A']),bool(f['expected_probe']['B'])])
 for name in ['A','B']:
  expected=expected_outputs(f,name);a(name+' exact receipt',r['calls'][name],old['calls'][name]);a(name+' frozen full outputs',r['calls'][name]['outputs'],expected)
  for b in r['budgets']:
   qb=next(z for z in old['budgets'][name]if z['q']==b['q']);a(name+' q'+str(b['q'])+' exact literal budget receipt',b[name],qb['receipt'])
  # Exact numeric color names differ from the own transcription; class equivalence must coincide.
  cls=[r['sectors'][0],r['sectors'][1],f['P'][1],f['P'][2]]if name=='A'else[f['P'][0],r['sectors'][2],r['sectors'][3],f['P'][2]]
  colors=dict(r['colors_'+name]);a(name+' four original color equivalence classes',len(set(colors.values()))==4 and all((colors[u]==colors[v])==any(u in b and v in b for b in cls)for u in colors for v in colors))
  for j,fac in enumerate(r['output_facts'][name]):
   e=old['hulls'][name][j];a(name+str(j)+' source hulls',fac['source_hulls'],e['source']);a(name+str(j)+' target hulls',fac['target_hulls'],e['target']);a(name+str(j)+' source embedding',fac['source_embeddings'],e['source_disjoint']);a(name+str(j)+' target embedding',fac['target_embeddings'],e['target_disjoint']);a(name+str(j)+' agreement distinct from embedding',fac['agreement'],e['agreement']);a(name+str(j)+' parent refinement',fac['parent_refinement']);a(name+str(j)+' proper source partition',fac['partition_source'])
   for b in fac['blocks']:a(name+str(j)+' exact block rooted topology '+str(b['labels']),b['good'],x.agrees(x.Graph(f['S']),x.Graph(f['T']),b['labels']))
 a('same appended raw list',r['appended_raw'],old['appended_raw'])
 for got,want in zip(r['masses'],old['masses']):
  c=F(got['c']['num'],got['c']['den']);v=F(got['value']['num'],got['value']['den']);a('actual rawQMass '+str(c),str(v),want['mass']);a('same literal raw denominator '+str(c),got['raw_denominator'],len(r['appended_raw']))
  if not f['cheap']:a('actual two-high bound '+str(c),v<=4*c**-4)
 if f['cheap']:
  own=f['cheap'];other='B'if own=='A'else'A';parent=f['P'][0 if own=='A'else 1];otherparent=f['P'][1 if own=='A'else 0];C=f['P'][2];fac=r['output_facts'][own][0]
  a('cheap source AND target embedding',fac['source_embeddings']and fac['target_embeddings']);a('cheap embedding is NOT agreement',fac['agreement'],False)
  if 'local'in f:local_compare(f,r['local_'+own],checks,prefix+'parent')
  else:
   bads=f['two_bad_blocks'];blocks=fac['blocks'];inds=[next(i for i,b in enumerate(blocks)if set(b['labels'])==set(z))for z in bads];a('two distinct actual bad emitted blocks',len(set(inds))==2 and all(not blocks[i]['good']for i in inds)and not(set(fac['target_hulls'][inds[0]])&set(fac['target_hulls'][inds[1]])))
  for j,of in enumerate(r['output_facts'][other]):
   bs=of['blocks'];ki=next((i for i,b in enumerate(bs)if set(b['labels'])==set(parent)),None);ci=next((i for i,b in enumerate(bs)if set(b['labels'])==set(C)),None);bp=[i for i,b in enumerate(bs)if set(b['labels'])<=set(otherparent)];a('opposite'+str(j)+' actual whole parent/C',ki is not None and ci is not None)
   hs=[set(z)for z in of['target_hulls']];a('opposite'+str(j)+' actual crossclear against parent/C',not(hs[ki]&hs[ci])and all(not(hs[i]&hs[ki])and not(hs[i]&hs[ci])for i in bp))
   overlap=any(hs[i]&hs[k]for u,i in enumerate(bp)for k in bp[u+1:]);a('opposite'+str(j)+' retained within-other target overlap',bool(overlap),f['opposite_within_other_overlap'][j])
   if 'local'in f:local_compare(f,bs[ki]['local'],checks,prefix+'opposite'+str(j));a('opposite'+str(j)+' identical compiled local restriction/certificate',bs[ki]['local'],r['local_'+own])
 return r
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('stage',choices=['pilot','battery']);arg=ap.parse_args();rows=parse('pilot-ReadoutPilot.log');checks=[];evaluate(bank['fixtures'][0],rows[0],ref['fixtures'][0],checks)
 if arg.stage=='battery':
  more=parse('battery-ReadoutBattery.log');rows+=more
  for f,r,old in zip(bank['fixtures'][1:],more[:4],ref['fixtures'][1:]):evaluate(f,r,old,checks)
  byid={r['id']:r for r in rows}
  for f in bank['outside']:
   r=byid[f['id']];add(checks,f['id']+' source P guard',r['source_P'],f['id']!='reused-source-overlap-outside');add(checks,f['id']+' C clearance guard',r['C_clear'],f['id']!='hand-C-clearance-corrupt-outside')
   for n in ['A','B']:
    old=next(z for z in ref['outside']if z['id']==f['id'])['calls'][n];add(checks,f['id']+' exact outside raw '+n,r['calls'][n],old)
  for n in ['root','leaf','absent']:
   r=byid['frozen-invalid-'+n+'-edge'];add(checks,n+' edge fails actual selected-edge equality',r['selector']!={'kind':'edge','edge':[r['edge'][:-1],r['edge']]})
 out={'stage':arg.stage,'checks':checks,'denominator':len(checks),'passed':sum(z['pass']for z in checks),'all_pass':all(z['pass']for z in checks),'fixture_expectations_changed':False,'fixtures_sha256':hashlib.sha256((READY/'fixtures-v1.json').read_bytes()).hexdigest(),'observations':rows,'replication_increment':0}
 (P/('compiled-'+arg.stage+'-comparison-v1.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['checks','observations']},indent=2));print('Failed:',[z['name']for z in checks if not z['pass']]);assert out['all_pass']
