"""One-shot greedy source-reachable obstruction synthesis, exact graph tests.
The objective is pre-registered emitted-cover mass, never optimum oracle calls.
"""
from scaffold_augment import *


def extend(w):
    start=time.perf_counter();t,s,ch=w['original_T'],w['original_Tprime'],w['cherry'];st,tt=Tree(s),Tree(t)
    ps=st.pendant(*ch);aa=set(next(z['labels'] for z in ps if 0 in z['labels']));ab=set(z for p in ps for z in p['labels'])
    sas=[tuple(map(int,p)) for p,l in st.below.items() if set(l)<=aa];tas=[tuple(map(int,p)) for p,l in tt.below.items() if set(l)<=ab]
    fresh=max(tt.labels)+1;counts={'candidate_pairs':0,'admitted':0,'pair_isolated_good_states':0,'expensive_boundaries':0,'raw_mass_ge1':0,'post_depth1_mass_ge1':0};best=None
    for sp in sas:
      ns=graft(s,sp,fresh)
      for tp in tas:
        nt=graft(t,tp,fresh);counts['candidate_pairs']+=1
        if not selected_valid(nt,ns,ch):continue
        counts['admitted']+=1;o=scan_child(nt,ns,ch)
        if o is None:continue
        counts['pair_isolated_good_states']+=1
        for r in o['expensive_boundaries']:
          counts['expensive_boundaries']+=1;raw=Fraction(r['raw_full_mass']);live=Fraction(r['unresolved_after_depth1_full_mass'])
          counts['raw_mass_ge1']+=raw>=1;counts['post_depth1_mass_ge1']+=live>=1
          key=(live,repr(nt),repr(ns),r['edge'])
          if best is None or key>best[0]:best=(key,{'source_address':sp,'target_address':tp,'state':o,'boundary':r})
    return {'n':len(tt.labels)+1,'new_label':fresh,'counts':counts,'best':best[1] if best else None,'elapsed_seconds':time.perf_counter()-start}

if __name__=='__main__':
    ctl=controls();initial=run_augment();w=initial['worst']['state'];stages=[];start=time.perf_counter()
    for step in range(5):
      out=extend(w);stages.append(out)
      print(json.dumps({k:v for k,v in out.items() if k!='best'}),flush=True)
      if not out['best'] or out['counts']['post_depth1_mass_ge1'] or out['elapsed_seconds']>60:break
      w=out['best']['state']
    record={'controls':ctl,'base_controls':initial['controls'],'stages':stages,'elapsed_seconds':time.perf_counter()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((HERE/'SCAFFOLD-AUGMENT-PIN-v2.json').read_bytes()).hexdigest(),'scope':'Finite greedy extension development. Any mass fire is selected emitted cover only until all selectors and source cases audited.'}
    (ROOT/'results/algorithm-universal233-scaffold-greedy-v1.json').write_text(json.dumps(record,indent=2)+'\n')
    print('Final post-depth1 mass:',stages[-1]['best']['boundary']['unresolved_after_depth1_full_mass'] if stages[-1]['best'] else 'no admitted extension')
