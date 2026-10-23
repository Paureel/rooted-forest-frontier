import copy,importlib.util,json,pathlib
P=pathlib.Path(__file__).resolve().parent;PRE=P.parent
s=importlib.util.spec_from_file_location('ownpre',PRE/'scoped_graph_v2.py');g=importlib.util.module_from_spec(s);s.loader.exec_module(g)
base=json.loads((PRE/'EXPECTATIONS-v1.json').read_text())['cases'];cases=copy.deepcopy(base)+[json.loads((PRE/'EXPECTATIONS-EXTENSION-v2.json').read_text())['case']]
def mirror(t):return t if isinstance(t,int) else [mirror(t[1]),mirror(t[0])]
def mp(x,m):return m.get(x,x) if isinstance(x,int) else [mp(a,m) for a in x]
v=copy.deepcopy(base[0]);v['id']='root-child-swap-T';v['T']=[v['T'][1],v['T'][0]];v['cutT']='0';v.pop('trees');v['hulls']['T']=[['' if not a else ('1' if a[0]=='0' else '0')+a[1:] for a in h] for h in v['hulls']['T']];cases.append(v)
v=copy.deepcopy(base[0]);v['id']='opposite-cut-sides';v['cutS']='0';cases.append(v)
v=copy.deepcopy(base[0]);v['id']='reverse-roles-refusal';v['X'],v['Y']=v['Y'],v['X'];v['repX'],v['repY']=v['repY'],v['repX'];v.pop('trees');fs=copy.deepcopy(v['minimum_families']);v['minimum_families']={'X':fs['Y'],'Y':fs['X'],'MX':mp(fs['MY'],{11:10}),'MY':mp(fs['MX'],{10:11}),'global':fs['global']};v['costs']={'X':1,'Y':0,'MX':1,'MY':0,'global':1};v['guard']='REFUSAL';v.pop('marked_outside_depth01');v['answers']={k:'REFUSAL' for k in v['answers']};cases.append(v)
v=copy.deepcopy(base[0]);v['id']='arbitrary-Nat';m={0:17,1:101,2:5,3:999,10:10000,11:10001}
for k in ['T','S','X','Y','repX','repY','rho','gamma']:v[k]=mp(v[k],m)
v['trees']={k:mp(t,m) for k,t in v['trees'].items()};v['minimum_families']={k:mp(F,m) for k,F in v['minimum_families'].items()};v['hulls']['forest']=mp(v['hulls']['forest'],m);cases.append(v)
v=copy.deepcopy(base[0]);v['id']='all-child-swaps';v['T']=mirror(v['T']);v['S']=mirror(v['S']);v['cutT']=v['cutS']='0';v.pop('trees')
for k in ['T','S']:v['hulls'][k]=[[''.join('1' if a=='0' else '0' for a in q) for q in H] for H in v['hulls'][k]]
cases.append(v)
