from pathlib import Path
import json,sys,shutil,subprocess,os,time,copy,argparse
H=Path(__file__).resolve().parent;ROOT=H.parents[5];B=H/'isolated';P=H.parent/'sol-frozen-ready-v1/preparation';sys.path.insert(0,str(P));import agreement_oracle_v2 as oracle;import dp_runtime_v1 as dp
LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
def tr(t):return f'(.leaf {t})' if isinstance(t,int) else f'(.node {tr(t[0])} {tr(t[1])})'
def opt(t):return 'none' if t is None else '(some '+tr(t)+')'
def ls(x):return '['+','.join(ls(v) if isinstance(v,list) else str(v) for v in x)+']'
def ss(s):return '['+','.join(tr(t) for t in s)+']'
def paint(t,a,assignment):return f'(.leaf {t} {assignment[a]})' if isinstance(t,int) else f'(.node {assignment[a]} {paint(t[0],a+"0",assignment)} {paint(t[1],a+"1",assignment)})'
def compare_state(f,row,spec):
 assert row['proper']==f['proper'] and row['allGood']==f['allGood'],('guard',f['id'])
 truth=oracle.summarize(f['T'],f['ss']);assert truth['minimum']==f['oracleMinimum'] and sorted(oracle.normalize_forest(v) for v in truth['minima'])==sorted(oracle.normalize_forest(v) for v in f['minima'])
 if not f['allGood']:assert row['run'] is None and row['paint'] is None and not any(row['decisions']);return
 F=oracle.normalize_forest(row['run']);assert F in [oracle.normalize_forest(v) for v in f['minima']] and oracle.agrees(f['T'],f['ss'],F) and row['acceptedAgrees'] is True
 assert row['cost']==len(F)-len(f['ss'])==f['oracleMinimum']>=0
 assert row['decisions']==[f['oracleMinimum']<=q for q in spec['q']]
 if f['T'] is None:assert row['paint'] is None and F==[];return
 G=dp.Graph(f['T']);v=row['paint'];assignment={tuple(int(c) for c in z['address']):z['color'] for z in v['vertices']};regions=dp.regions(G,assignment)
 assert len(assignment)==len(G.child)==v['treeVertices']==f['visits'];assert all(r['leaves'] for r in regions)
 assert oracle.normalize_forest([r['leaves'] for r in regions])==F==oracle.normalize_forest(v['rawBlocks'])
 assert v['changes']==f['changes']==len(regions)-1 and len(regions)==f['regions']
 assert sum(assignment[a]!=assignment[b] for a,cs in G.child.items() for b in cs)==v['changes']
 owner=dp.owners(f['T'],f['ss']);assert dict(row['owners'])==owner
 for a,x in G.taxon.items():assert assignment[a]==owner[x]
 actual_rows={z['address']:{str(c['color']):c['changes'] for c in z['candidates']} for z in v['rows']}
 assert all(len(z['candidates'])==len(f['ss'])==len(set(c['color'] for c in z['candidates'])) for z in v['rows'])
 independent=dp.run(f['T'],f['ss']);assert actual_rows==independent['internalRows']
 if f['id'] in spec['internalRows']:assert actual_rows==spec['internalRows'][f['id']]

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--pilot',action='store_true');args=ap.parse_args();spec=json.loads((P/'EXPECTATIONS-v1.json').read_text());fixed=json.loads((P/'fixed-timed-v2.json').read_text());fixtures=spec['fixtures'][:3] if args.pilot else spec['fixtures'];commands=['import NativeAdapter','open SolNative']
 for f in fixtures:commands.append(f'#eval emit "STATE" (stateRecord {json.dumps(f["id"])} {opt(f["T"])} {ss(f["ss"])} {ls(spec["q"])})')
 forests=[]
 if not args.pilot:
  byid={f['id']:f for f in spec['fixtures']}
  for r in fixed['rows']:
   f=byid[r['id']]
   for i,record in enumerate(r['oracle']['records']):
    tag=f['id']+':partition:'+str(i);F=record['F'];forests.append((tag,f,F,record));commands.append(f'#eval emit "FOREST" (forestRecord {json.dumps(tag)} {opt(f["T"])} {ss(f["ss"])} {ls(F)})')
  for i,e in enumerate(spec['explicitForests']):
   f=byid[e['fixture']];tag='explicit:'+str(i);forests.append((tag,f,e['F'],e));commands.append(f'#eval emit "FOREST" (forestRecord {json.dumps(tag)} {opt(f["T"])} {ss(f["ss"])} {ls(e["F"])})')
  for i,g in enumerate(spec['geometry']):commands.append(f'#eval emit "GEOMETRY" (geometryRecord "geometry:{i}" {tr(byid[g["fixture"]]["T"])} {ls(g["B"])})')
  raw=spec['leaflessRawControl'];f=byid[raw['fixture']];p=paint(f['T'],'',raw['assignment']);commands.append(f'#eval emit "RAW" (Lean.Json.mkObj [("vertices",Lean.toJson (paintVertices "" {p})),("changes",Lean.toJson (changes {p})),("rawBlocks",Lean.toJson (rawBlocks {p})),("blocks",Lean.toJson (blocks {p}))])')
 commands.insert(1,'open RMAF ForestState AllGoodDP')
 file=B/('ProbeNativePilot.lean' if args.pilot else 'ProbeNativeFixed.lean');file.write_text('\n'.join(commands)+'\n');shutil.copyfile(H/'NativeAdapter-v1.lean',B/'NativeAdapter.lean');procs=[];start=time.perf_counter();tag='pilot' if args.pilot else 'fixed'
 tasks=[('compile-native-adapter',['-o','NativeAdapter.olean','NativeAdapter.lean']),('native-'+tag,[file.name])] if args.pilot else [('native-'+tag,[file.name])]
 for label,cmd in tasks:
  t=time.perf_counter();r=subprocess.run([str(LEAN),*cmd],cwd=B,env={**os.environ,'LEAN_PATH':str(B)},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60);(H/(label+'-v2.log')).write_text(r.stdout);procs.append({'label':label,'seconds':time.perf_counter()-t,'exit':r.returncode});assert r.returncode==0,(label,r.stdout[:2000])
 rows={k:[] for k in ['STATE','FOREST','GEOMETRY','RAW']}
 for line in (H/('native-'+tag+'-v2.log')).read_text().splitlines():
  for k in rows:
   if line.startswith(k+'\t'):rows[k].append(json.loads(line[len(k)+1:]))
 assert len(rows['STATE'])==len(fixtures)
 for f,r in zip(fixtures,rows['STATE']):assert f['id']==r['id'];compare_state(f,r,spec)
 assert len(rows['FOREST'])==len(forests)
 for (tag,f,F,truth),r in zip(forests,rows['FOREST']):assert r['id']==tag and r['F']==F and r['agrees']==truth['valid']==oracle.agrees(f['T'],f['ss'],F) and r['costNat']==max(0,len(F)-len(f['ss']))
 catches=[]
 if not args.pilot:
  for g,r in zip(spec['geometry'],rows['GEOMETRY']):assert sorted(r['hull'])==g['hull'] and dp.canonical(r['restriction'])==dp.canonical(g['restriction'])
  assert len(rows['GEOMETRY'])==3 and len(rows['RAW'])==1
  raw=spec['leaflessRawControl'];r=rows['RAW'][0];a={tuple(map(int,v['address'])):v['color'] for v in r['vertices']};regions=dp.regions(dp.Graph(byid[raw['fixture']]['T']),a);assert regions==raw['regions'] and r['changes']==4 and len(r['rawBlocks'])==5 and sum(not b for b in r['rawBlocks'])==2
  assert oracle.normalize_forest(r['blocks'])==raw['droppedForest'] and len(r['rawBlocks'])-2==raw['rawRegionOffset']!=raw['droppedForestCost']
  target=next(f for f in fixtures if f['id']=='balanced-cross');actual=next(r for r in rows['STATE'] if r['id']=='balanced-cross')
  mutations=['bad-guard','invalid-overlap-forest','valid-nonminimum-forest','bad-source-offset','missing-root-color','leafless-final-paint','false-budget']
  for m in mutations:
   c=copy.deepcopy(actual)
   if m=='bad-guard':c['allGood']=False
   elif m=='invalid-overlap-forest':c['run']=[[0,2],[1,3]]
   elif m=='valid-nonminimum-forest':c['run']=[[0],[1],[2],[3]];c['cost']=2
   elif m=='bad-source-offset':c['cost']=0
   elif m=='missing-root-color':c['paint']['rows'][0]['candidates'].pop()
   elif m=='leafless-final-paint':c['paint']['vertices'][0]['color']=100
   else:c['decisions'][0]=True
   try:compare_state(target,c,spec)
   except AssertionError:catches.append(m)
   else:raise AssertionError(('native comparator accepted corruption',m))
 out={'status':'NATIVE-COMPARISONS-PASS','pilot':args.pilot,'fixtures':len(fixtures),'forestComparisons':len(forests),'minimumWitnessCountInFrozenBank':sum(len(f['minima']) for f in spec['fixtures']),'rows':rows,'catches':catches,'processes':procs,'seconds':time.perf_counter()-start,'independentReplicaIncrement':0};(H/('native-'+('pilot' if args.pilot else 'fixed')+'-v2.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
if __name__=='__main__':main()
