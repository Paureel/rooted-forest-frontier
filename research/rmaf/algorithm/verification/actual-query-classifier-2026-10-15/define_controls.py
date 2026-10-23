"""Hand-expanded fixed expectations; no instrument imports/evaluations."""
from pathlib import Path
import json
b=Path(__file__).resolve().parent;cs=[]
def z(t):return {'kind':'zero','target':t}
def omit(t):return {'kind':'omit','target':t}
def val(t,x):return {'kind':'value','target':t,'replacement':x}
def meta(t,x):return {'kind':'metadata','target':t,'replacement':x}
def add(id,op,d,v,counts={},metadata={},plants=[]):
 cs.append({'id':id,'op':op,'input':d,'value_fields':v,'counts':counts,'metadata':metadata,'plants':plants,'positive_counts':[p['target'] for p in plants if p['kind'] in ['zero','omit'] and counts.get(p['target'],1)!=0]})
def qcase(id,q,minima,slots=None,resolved=[],v={},counts={},plants=[]):
 d={'q':q,'minima':minima,'slots':slots or [chr(65+i) for i in range(len(minima))],'resolved':resolved};add(id,'query',d,v,counts,{},plants)
qcase('two-budget3-successes-total6-reject',5,[3,3],v={'accepted':False,'reason':'sum','budget':3,'cost':6,'bad':2,'trace.0.budget':3,'trace.1.budget':3,'mass.2.exact':'1/2','mass.233/100.exact':'20000/54289','mass.3.exact':'2/9'},counts={'query.actual_calls':2,'query.final_sum_check':1,'query.returned_sum_cells':2},plants=[val('accepted',True),z('query.final_sum_check'),{'kind':'omit_trace'},{'kind':'duplicate_trace'},val('trace.1.budget',2)])
qcase('known1-one-min4-total5-accept',5,[4],resolved=[{'slot':'R','cost':1,'witness':'resolved-r'}],v={'accepted':True,'budget':4,'cost':5,'bad':2,'discount_eligible':True,'mass.2.exact':'1/2','mass.233/100.exact':'100/233','mass.3.exact':'1/3'},counts={'query.actual_calls':1,'query.resolved_cells':1},plants=[val('budget',5),{'kind':'wrong_IH'},z('query.resolved_cells')])
qcase('sole-hard-budget5-no-discount',5,[5],v={'accepted':True,'budget':5,'cost':5,'bad':1,'discount_eligible':False,'mass.2.exact':'1','mass.2.discount_holds':False,'mass.233/100.exact':'1','mass.3.exact':'1'},counts={'query.actual_calls':1},plants=[val('trace.0.budget',4),val('mass.2.exact','1/2'),val('discount_eligible',True),meta('minima_access_in_caller',True)])
qcase('q3-two-hard-slots-early-no-calls',3,[2,2],v={'accepted':False,'reason':'early','budget':None,'trace':[],'mass.2.exact':'0'},counts={'query.actual_calls':0,'query.budget_arithmetic':0,'query.pretest':1},plants=[val('budget',1),omit('query.pretest'),val('accepted',True)])
qcase('q6-three-min2-budget2-all-accept',6,[2,2,2],v={'accepted':True,'budget':2,'cost':6,'bad':3,'trace.2.slot':'C','mass.2.exact':'3/16','mass.233/100.exact':'300000000/2947295521','mass.3.exact':'1/27'},counts={'query.actual_calls':3,'query.returned_sum_cells':3},plants=[{'kind':'omit_trace'},val('trace.2.index',1),z('query.returned_sum_cells'),{'kind':'wrong_IH'}])
qcase('first-failure-is-actual-call-and-stops',5,[4,2],v={'accepted':False,'reason':'failure','budget':3,'cost':0,'trace.0.success':False,'mass.2.exact':'1/4','mass.233/100.exact':'10000/54289','mass.3.exact':'1/9'},counts={'query.actual_calls':1,'query.trace_cells':1,'query.final_sum_check':0},plants=[{'kind':'omit_trace'},val('mass.2.exact','1/2'),z('query.actual_calls')])
qcase('middle-failure-executed-prefix-only',6,[2,3,2],v={'accepted':False,'reason':'failure','cost':2,'budget':2,'trace.1.slot':'B','trace.1.success':False,'mass.2.exact':'1/8','mass.233/100.exact':'200000000/2947295521','mass.3.exact':'2/81'},counts={'query.actual_calls':2},plants=[{'kind':'duplicate_trace'},val('trace.1.slot','C'),val('mass.2.exact','3/16')])
qcase('last-failure-retains-three-calls',6,[2,2,3],v={'accepted':False,'reason':'failure','cost':4,'trace.2.success':False,'mass.2.exact':'3/16'},counts={'query.actual_calls':3},plants=[{'kind':'omit_trace'},val('accepted',True)])
qcase('no-slots-q0-accept-empty',0,[],v={'accepted':True,'reason':'accept','cost':0,'trace':[],'budget':0,'mass.2.exact':'0'},counts={'query.actual_calls':0,'query.final_sum_check':1},plants=[z('query.final_sum_check'),val('accepted',False)])
qcase('no-unresolved-known5-accept',5,[],resolved=[{'slot':'R','cost':5,'witness':'known5'}],v={'accepted':True,'cost':5,'trace':[],'mass.2.exact':'0'},counts={'query.actual_calls':0,'query.resolved_cells':1},plants=[z('query.resolved_cells'),val('cost',0)])
qcase('excess-known-cost-rejects-before-call',5,[],resolved=[{'slot':'R','cost':6,'witness':'known6'}],v={'accepted':False,'reason':'early','cost':6,'budget':None,'trace':[]},counts={'query.actual_calls':0,'query.budget_arithmetic':0},plants=[val('accepted',True),val('budget',0)])
qcase('zero-resolved-cost-not-bad-slot',5,[5],resolved=[{'slot':'R','cost':0,'witness':'zero'}],v={'accepted':True,'budget':5,'bad':1,'discount_eligible':False,'mass.2.exact':'1','mass.2.discount_holds':False},counts={'query.actual_calls':1},plants=[val('bad',2),val('discount_eligible',True)])
qcase('two-positive-resolved-slots-zero-mass',5,[],resolved=[{'slot':'R','cost':1,'witness':'one'},{'slot':'S','cost':2,'witness':'two'}],v={'accepted':True,'cost':3,'bad':2,'discount_eligible':True,'mass.2.exact':'0'},counts={'query.actual_calls':0,'query.resolved_cells':2},plants=[val('bad',0),z('query.resolved_cells')])
qcase('duplicate-slot-ids-retain-position-and-mass',4,[2,2],slots=['X','X'],v={'accepted':True,'budget':2,'cost':4,'trace.0.slot':'X','trace.1.slot':'X','trace.1.index':1,'mass.2.exact':'1/2'},counts={'query.actual_calls':2,'query.trace_cells':2},plants=[{'kind':'omit_trace'},{'kind':'duplicate_trace'},val('trace.1.index',0)])
qcase('mixed-known-and-two-hard-budget2',6,[2,2],resolved=[{'slot':'R','cost':0,'witness':'zero'},{'slot':'S','cost':2,'witness':'two'}],v={'accepted':True,'budget':2,'cost':6,'bad':3,'mass.2.exact':'1/8'},counts={'query.actual_calls':2,'query.resolved_cells':2},plants=[val('trace.0.budget',3),z('query.returned_sum_cells')])
H=2**128
qcase('large-q-scalar-budget-preserved',H,[4],resolved=[{'slot':'R','cost':1,'witness':'one'}],v={'accepted':True,'budget':H-1,'trace.0.budget':H-1,'cost':5,'mass.2.exact':'1/2'},counts={'query.actual_calls':1},plants=[meta('q_bits',1),val('trace.0.budget',5)])
cs[-1]['metadata']['q_bits']=129
for n,cells in [(8,28),(64,2016)]:
 add('trace-builder-left-copy-'+str(n),'trace_builder',{'calls':n},{'trace':list(range(n)),'calls':n,'linear_cons_reverse_cells':2*n},{'trace_builder.append_calls':n,'trace_builder.left_cells':cells,'trace_builder.cell_upper_ops':8*cells},{},[z('trace_builder.left_cells'),z('trace_builder.cell_upper_ops'),{'kind':'duplicate_record'}])
cheap=[[[0,1],[2,3]],[[4,5],[6,7]]];high=[[[0,2],[1,3]],[[4,5],[6,7]]]
C={'partition':[[4,5],[2,3],[0,1],[6,7]],'cuts':['10','01','00']}
H0={'partition':[[1],[0],[6,7],[4,5],[2,3]],'cuts':['010','000','11','10']}
H1={'partition':[[3],[2],[6,7],[4,5],[0,1]],'cuts':['011','001','11','10']}
for name,t,outputs in [('cheap',cheap,[C]),('high',high,[H0,H1])]:
 for q in [0,2,3,4,H]:
  below=q<3;cheap_accept=name=='cheap' and not below
  calls=0 if below else (1 if cheap_accept else 2);colors=8*calls
  out=[] if below or (name=='high' and q==3) else outputs
  v={'outputs':out,'costs':[len(x['cuts']) for x in out],'path':'below-three' if below else ('reuse' if cheap_accept else 'full'),'rank_calls':0}
  if not below:v['trace.0.budget']=3;v['trace.0.phase']='probe'
  if calls==2:v['trace.1.budget']=q;v['trace.1.phase']='full'
  plants=[val('rank_calls',8)]
  if below:plants += [val('path','reuse'),val('outputs',[C])]
  else:
   plants += [z('probe.color_calls'),z('probe.generate_calls')]
   if out:plants += [val('outputs',out[:-1]),val('costs',[])]
   if calls==2:plants += [val('trace.1.budget',3 if q!=3 else 2)]
  add(name+'-known-four-q'+('huge' if q==H else str(q)),'classify',{'q':q,'source':t},v,{'probe.generate_calls':calls,'probe.color_calls':colors,'probe.oracle_tariff':colors},{'q_bits':129 if q==H else max(1,q.bit_length())},plants)
mirror=[[[1,0],[3,2]],[[5,4],[7,6]]];MC={'partition':[[5,4],[3,2],[1,0],[7,6]],'cuts':['10','01','00']}
add('cheap-preserves-within-block-leaf-order','classify',{'q':3,'source':mirror},{'outputs':[MC],'costs':[3],'path':'reuse'},{'probe.color_calls':8},{},[val('outputs',[C]),z('probe.color_calls')])
add('high-preserves-both-records-and-order','classify',{'q':4,'source':high},{'outputs':[H0,H1],'costs':[4,4],'path':'full'},{'probe.color_calls':16},{},[val('outputs',[H1,H0]),val('outputs',[H0]),val('outputs.0.cuts',['000','010','11','10']),val('outputs.0.partition',list(reversed(H0['partition'])))])
for name,t,calls in [('cheap',cheap,8),('high',high,16)]:
 add(name+'-expensive-callback-is-external-bill','classify',{'q':4,'source':t,'tariff':1000},{'costs':[3] if name=='cheap' else [4,4]},{'probe.color_calls':calls,'probe.oracle_tariff':calls*1000},{'tariff':1000},[z('probe.oracle_tariff'),meta('tariff',1)])
add('duplicate-leaf-refusal-never-evaluates-color','classify',{'q':4,'source':[0,0]}, {'outputs':[],'costs':[],'path':'full','trace.0.callbacks':0,'trace.1.callbacks':0},{'probe.generate_calls':2,'probe.color_calls':0},{},[val('trace.0.callbacks',2),val('path','reuse')])
def shift(t):return t+H if isinstance(t,int) else [shift(t[0]),shift(t[1])]
SC={'partition':[[H+4,H+5],[H+2,H+3],[H,H+1],[H+6,H+7]],'cuts':['10','01','00']}
add('huge-labels-four-colors-not-four-small-identifiers','classify',{'q':3,'source':shift(cheap)}, {'outputs':[SC],'costs':[3],'path':'reuse'},{'probe.color_calls':8},{'label_bits':129,'symbolic_floor_color_bits':128},[meta('label_bits',3),meta('symbolic_floor_color_bits',2),z('probe.color_calls')])
add('generic-inputRank-additional-color-and-dedup-work','rank',{'source':cheap,'tariff':1000},{'rank':4,'values':[0,0,1,1,2,2,3,3],'colors':[0,1,2,3]},{'rank.color_calls':8,'rank.oracle_tariff':8000,'rank.equality_calls':16},{},[z('rank.color_calls'),z('rank.oracle_tariff'),z('rank.equality_calls')])
pin={'phase':'PRE-CANDIDATE hand-expanded mocks,exact rational formulae and raw source records;no instrument output or candidate source','controls':cs,'declared_controls':len(cs),'declared_plants':sum(len(c['plants']) for c in cs),'pilot_ids':['two-budget3-successes-total6-reject','sole-hard-budget5-no-discount','cheap-known-four-q3'],'size_pilot_ids':['q6-three-min2-budget2-all-accept','high-known-four-q4','trace-builder-left-copy-64','high-known-four-qhuge']}
(b/'CONTROL-PIN.json').write_text(json.dumps(pin,indent=2)+'\n');print(json.dumps({k:v for k,v in pin.items() if k!='controls'}))
