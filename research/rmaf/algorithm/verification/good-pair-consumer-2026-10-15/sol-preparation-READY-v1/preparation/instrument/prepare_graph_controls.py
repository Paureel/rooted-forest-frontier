#!/usr/bin/env python3
"""One-shot prerelease review controls; reuses the disclosed X0 checker lineage.
No candidate code, optimum oracle in runtime, or universal proof is present.
"""
import argparse
import copy
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from pathlib import Path
import time
HERE=Path(__file__).resolve().parent.parent
sp=importlib.util.spec_from_file_location('x0_reused',HERE/'instrument/x0_evaluator_reused.py')
x=importlib.util.module_from_spec(sp);sp.loader.exec_module(x)

def regions(g,v,selected):
    if v not in g.adj: return []
    result=[]
    for neighbor in sorted(g.adj[v]):
        seen={v}; stack=[neighbor]; component=set()
        while stack:
            z=stack.pop()
            if z in seen:continue
            seen.add(z);component.add(z);stack.extend(g.adj[z]-seen)
        labs=sorted(a for a,p in g.at.items() if p in component and a in selected)
        if labs:result.append({'neighbor':neighbor,'labels':labs})
    return result

def refines(fine,coarse):
    return all(any(set(b)<=set(c) for c in coarse) for b in fine)

def premises(f):
    s,t=x.Graph(f['S']),x.Graph(f['T']); A,B,C=f['P']
    return {'same_distinct_labels':s.distinct and t.distinct and set(s.labels)==set(t.labels),
            'proper_P':x.proper(s.labels,f['P']), 'source_P_disjoint':s.disjoint(f['P']),
            'A_good':x.agrees(s,t,A),'A_B_target_overlap':bool(t.hull(A)&t.hull(B)),
            'C_clear':not bool(t.hull(C)&(t.hull(A)|t.hull(B)))}

def calls_for(f,q):
    t=x.Graph(f['T']);A,B,C=f['P']
    if 'vertex' in f:
        v=f['vertex'];ar=[z['labels'] for z in regions(t,v,set(A))];br=[z['labels'] for z in regions(t,v,set(B))]
        specs=[('clear-A',ar+[B,C]),('clear-B',[A]+br+[C])]
    else:
        D=t.desc[f['edge']]; specs=[('edge-clear-B',[A,sorted(set(B)&D),sorted(set(B)-D),C])]
    return [{'identity':name,'colors':{a:i for i,b in enumerate(bs) for a in b},
             'receipt':x.generate(f['S'],{a:i for i,b in enumerate(bs) for a in b},q)} for name,bs in specs]

def raw_outputs(calls):return [o for c in calls for o in c['receipt']['outputs']]
def mass(calls,c):return sum((c**(-len(o['sourceCuts'])) for o in raw_outputs(calls)),F())
def source_valid(f,o):
    s=x.Graph(f['S']);cp=s.cut_parts(o['sourceCuts'])
    return cp is not None and cp['parts']==x.canon(o['partition']) and not cp['empty_components'] and cp['graph_components']==len(o['sourceCuts'])+1 and x.proper(s.labels,o['partition']) and s.disjoint(o['partition']) and refines(o['partition'],f['P'])

def analyze(f):
    start=time.perf_counter();s,t=x.Graph(f['S']),x.Graph(f['T']); calls=calls_for(f,f['q']);outs=raw_outputs(calls)
    agreements=[bs for bs in x.refinements(f['P']) if x.agreement(s,t,s.labels,bs)]
    out={'id':f['id'],'premises':premises(f),'calls':calls,'source_valid_each':[source_valid(f,o) for o in outs],
         'Q_agreement_each':[x.agreement(s,t,s.labels,o['partition']) for o in outs],
         'additional_queries':[x.optimum(s,t,o['partition']) for o in outs],
         'optimum_refining_P':x.optimum(s,t,f['P']), 'mass':{str(F(*cc)):str(mass(calls,F(*cc))) for cc in data['rational_c']},
         'budgets':[]}
    for q in range(f['q']+1):
        cc=calls_for(f,q); oo=raw_outputs(cc);eligible=[bs for bs in agreements if len(bs)-1<=q];checks=[]
        for fs in eligible:
            witness=None
            for o in oo:
                opt=x.optimum(s,t,o['partition'])
                if opt['components']<=len(fs):witness={'Q':o,'Fprime':opt['witness'],'F_components':len(fs),'Fprime_components':opt['components']};break
            checks.append({'F':x.canon(fs),'exists_no_larger_Fprime':witness is not None,'witness':witness})
        out['budgets'].append({'q':q,'call_costs':[[len(o['sourceCuts']) for o in c['receipt']['outputs']] for c in cc],
                               'eligible_F_denominator':len(eligible),'covered':sum(z['exists_no_larger_Fprime'] for z in checks),'checks':checks})
    actual={'all_premises':all(out['premises'].values()),'A_good':out['premises']['A_good'],
            'optimum_refining_P_components':out['optimum_refining_P']['components'],
            'refinement_partition_denominator':out['optimum_refining_P']['partition_denominator'],
            'agreement_count':len(agreements),'all_Q_agreement':all(out['Q_agreement_each']),
            'mass_c2':str(mass(calls,F(2))), 'each_Q_additional_cuts':[z['additional'] for z in out['additional_queries']]}
    if 'vertex' in f:
        ar,br=regions(t,f['vertex'],set(f['P'][0])),regions(t,f['vertex'],set(f['P'][1]))
        out['regions']={'A':ar,'B':br}
        actual.update({'A_region_count':len(ar),'B_region_count':len(br),'A_colors':len(set(calls[0]['colors'].values())),
                       'B_colors':len(set(calls[1]['colors'].values())),
                       'LA_costs':[len(o['sourceCuts']) for o in calls[0]['receipt']['outputs']],
                       'LB_costs':[len(o['sourceCuts']) for o in calls[1]['receipt']['outputs']],
                       'LA_cuts':[o['sourceCuts'] for o in calls[0]['receipt']['outputs']],
                       'LB_cuts':[o['sourceCuts'] for o in calls[1]['receipt']['outputs']],
                       'at_q3_LA_costs':out['budgets'][3]['call_costs'][0],
                       'at_q3_LB_costs':out['budgets'][3]['call_costs'][1],
                       'root_degree':len(t.adj['']),'root_A_regions':len(regions(t,'',set(f['P'][0]))),
                       'root_B_regions':len(regions(t,'',set(f['P'][1]))),
                       'selected_singleton_leaf_regions':len(regions(t,t.at[0],{0}))})
    else:
        A=set(f['P'][0]); B=set(f['P'][1]);D=t.desc[f['edge']]
        actual.update({'costs':[len(o['sourceCuts']) for o in outs],
                       'F_agreement':x.agreement(s,t,s.labels,f['F']),
                       'Fprime_agreement':x.agreement(s,t,s.labels,f['Fprime']),
                       'Fprime_no_larger':len(f['Fprime'])<=len(f['F']),
                       'F_refines_any_Q':any(refines(f['F'],o['partition']) for o in outs),
                       'Fprime_refines_some_Q':any(refines(f['Fprime'],o['partition']) for o in outs),
                       'kept_A_each':all(sum(set(b)==A for b in o['partition'])==1 for o in outs),
                       'clear_B_each':all(all(not(t.hull(b)&t.hull(A)) and (set(b)<=D or set(b).isdisjoint(D)) for b in o['partition'] if set(b)<=B) for o in outs),
                       'at_q3_costs':out['budgets'][3]['call_costs'][0],'at_q4_costs':out['budgets'][4]['call_costs'][0]})
        out['edge_trace']={'edge':f['edge'],'subtree_descendants':sorted(D),'sectors_A':[sorted(A&D),sorted(A-D)],'sectors_B':[sorted(B&D),sorted(B-D)],
                           'all_sectors_nonempty':all([A&D,A-D,B&D,B-D]),
                           'mutual_clear':all(not(t.hull(z)&t.hull(B)) for z in [A&D,A-D]) and all(not(t.hull(z)&t.hull(A)) for z in [B&D,B-D])}
    out['expectation_checks']=[{'field':k,'expected':v,'actual':actual[k],'pass':actual[k]==v} for k,v in f['expected'].items()]
    out['seconds']=time.perf_counter()-start
    out['pass']=all(c['pass'] for c in out['expectation_checks']) and all(out['source_valid_each']) and all(z['covered']==z['eligible_F_denominator'] for z in out['budgets'])
    return out

class UnknownFRead(RuntimeError):pass
class RuntimeInputs:
    def __init__(self,f):self.fixture=f
    @property
    def unknown_F(self):raise UnknownFRead('Runtime attempted to inspect unknown F')
def runtime_clean(inputs,q):return calls_for(inputs.fixture,q)
def runtime_false(inputs,q):return inputs.unknown_F

def controls():
    checks=[]
    def add(name,got,want=True):checks.append({'name':name,'got':got,'expected':want,'pass':got==want})
    vf=data['fixtures'][0];ef=data['fixtures'][1];cc=calls_for(vf,vf['q']);expected_ids=['clear-A','clear-B']
    add('clean two-call identities',[z['identity'] for z in cc]==expected_ids)
    add('omitted call caught',[z['identity'] for z in cc[1:]]!=expected_ids)
    dup=copy.deepcopy(cc);dup[1]['receipt']['outputs']+=copy.deepcopy(dup[1]['receipt']['outputs'])
    add('duplicate exact mass',str(mass(dup,F(2))),data['corruption_expectations']['vertex_duplicated_B_output_mass_c2'])
    dedup=[dict(o) for o in {json.dumps(o,sort_keys=True):o for o in raw_outputs(dup)}.values()]
    add('raw deduplication caught',len(dedup)!=len(raw_outputs(dup)) and mass(dup,F(2))!=mass(cc,F(2)))
    clean=raw_outputs(cc)[0];bad=copy.deepcopy(clean);bad['sourceCuts'].pop()
    add('clean source cuts',source_valid(vf,clean));add('wrong source-cut cost caught',source_valid(vf,bad),False)
    qo=raw_outputs(calls_for(ef,ef['q']))
    add('forged original F refinement caught',any(refines(ef['F'],o['partition']) for o in qo),False)
    add('replacement Fprime refinement clean',any(refines(ef['Fprime'],o['partition']) for o in qo))
    inputs=RuntimeInputs(vf);add('clean runtime without F allowed',len(runtime_clean(inputs,3))==2)
    caught=False
    try:runtime_false(inputs,3)
    except UnknownFRead:caught=True
    add('unknown-F runtime access caught',caught)
    for f in data['premise_corruptions']:
        g=premises(f);add(f['id']+' precise missing premise',[k for k,v in g.items() if not v],[f['expected_false_guard']])
    s=x.Graph([[0,1],2]);add('identical local pair zero-cut',x.optimum(s,s,[s.labels])['additional'],0)
    add('empty selection rejected',x.agrees(s,s,[]),False);add('absent selection rejected',x.agrees(s,s,[99]),False)
    r=x.generate([0,0],{0:0},3);add('duplicate label refused',r['refusals'],['duplicate original label'])
    sw=x.Graph([2,[1,0]]);add('sibling order irrelevant',x.agrees(s,sw,[0,1,2]))
    add('singleton topology',x.agrees(s,sw,[0]));add('invalid duplicate partition',x.agreement(s,s,s.labels,[[0,1],[1,2]]),False)
    return checks

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('stage',choices=['controls','pilot','battery']);a=ap.parse_args()
    data=json.loads((HERE/'fixtures-v1.json').read_text());start=time.perf_counter()
    out={'phase':'PRE-CANDIDATE PREPARATION ONLY','stage':a.stage,'instrument_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'fixture_sha256':hashlib.sha256((HERE/'fixtures-v1.json').read_bytes()).hexdigest(),'candidate_contact':False,'candidate_compilation':False,'replication_increment':0}
    if a.stage=='controls':
        z=controls();out['controls']=z;out['denominator']=len(z);out['passed']=sum(v['pass'] for v in z);ok=all(v['pass'] for v in z)
    else:
        selected=data['fixtures'][:1] if a.stage=='pilot' else data['fixtures'][1:];out['fixtures']=[]
        for f in selected:
            z=analyze(f);out['fixtures'].append(z)
            if not z['pass']:break
        out['denominator']=len(selected);out['completed']=len(out['fixtures']);out['passed']=sum(v['pass'] for v in out['fixtures']);ok=out['completed']==out['denominator'] and out['passed']==out['denominator']
    out['all_pass']=ok;out['seconds']=time.perf_counter()-start
    (HERE/('graph-'+a.stage+'-v1.json')).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['controls','fixtures']},indent=2))
    raise SystemExit(0 if ok else 1)
