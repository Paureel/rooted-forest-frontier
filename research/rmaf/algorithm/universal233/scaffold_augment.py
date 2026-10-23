"""One-shot source-eligible witness extension; no optimal oracle in production.
See frozen augment pin for the exact candidate and rejection criteria.
"""
from scaffold_graft_search import *


def selected_valid(t,s,ch):
    tt,st=Tree(t),Tree(s)
    return (sorted(ch) in tt.cherries() and
            applicability(tt,st)['excluded_2a_to_2d'] and applicability(st,tt)['excluded_2a_to_2d'])


def run_augment():
    start=time.perf_counter();pin=json.loads((HERE/'SCAFFOLD-AUGMENT-PIN-v1.json').read_text())
    base=json.loads((ROOT/'results/algorithm-universal233-scaffold-witness-v1.json').read_text())
    w=base['witness'];t,s,ch=w['original_T'],w['original_Tprime'],w['cherry']
    assert selected_valid(t,s,ch) and not selected_valid(t,s,[0,1])
    baseout=scan_child(t,s,ch);assert baseout is not None
    assert any(r['raw_full_mass']==pin['base_expected']['raw_full_mass'] and r['unresolved_after_depth1_full_mass']==pin['base_expected']['unresolved_full_mass'] for r in baseout['expensive_boundaries'])
    aa=set(pin['base_expected']['source_A_labels']);bb={5,6};st,tt=Tree(s),Tree(t)
    sas=[tuple(int(x) for x in p) for p,l in st.below.items() if set(l)<=aa]
    tas=[tuple(int(x) for x in p) for p,l in tt.below.items() if set(l)<=aa|bb]
    fresh=max(tt.labels)+1;count={'candidate_pairs':0,'selected_and_earlier_admitted':0,'pair_isolated_good_states':0,'expensive_boundaries':0,'boundaries_raw_mass_ge1':0,'boundaries_after_depth1_mass_ge1':0};worst=None;witnesses=[]
    for sp in sas:
      ns=graft(s,sp,fresh)
      for tp in tas:
        nt=graft(t,tp,fresh);count['candidate_pairs']+=1
        if not selected_valid(nt,ns,ch):continue
        count['selected_and_earlier_admitted']+=1;o=scan_child(nt,ns,ch)
        if o is None:continue
        count['pair_isolated_good_states']+=1
        for r in o['expensive_boundaries']:
          count['expensive_boundaries']+=1
          raw=Fraction(r['raw_full_mass']);live=Fraction(r['unresolved_after_depth1_full_mass'])
          count['boundaries_raw_mass_ge1']+=raw>=1;count['boundaries_after_depth1_mass_ge1']+=live>=1
          if worst is None or live>Fraction(worst['boundary']['unresolved_after_depth1_full_mass']):worst={'source_address':sp,'target_address':tp,'state':o,'boundary':r}
          if live>=1 and not witnesses:witnesses.append({'source_address':sp,'target_address':tp,'state':o,'boundary':r})
    return {'counts':count,'worst':worst,'first_fire':witnesses,'controls':{'base_exact_masses_reconstructed':True,'noncherry_control_rejected':True},'elapsed_seconds':time.perf_counter()-start,'scope':'Finite development extension, selected-boundary pretest mechanism only; no universal assertion'}

if __name__=='__main__':
    out={'controls':controls(),'search':run_augment(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((HERE/'SCAFFOLD-AUGMENT-PIN-v1.json').read_bytes()).hexdigest()}
    (ROOT/'results/algorithm-universal233-scaffold-augment-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out['search'].items() if k not in ['worst','first_fire']}))
    if out['search']['worst']:print('Worst post-depth1 mass:',out['search']['worst']['boundary']['unresolved_after_depth1_full_mass'])
