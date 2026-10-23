"""One-shot X0 of the exact paid pair-continuation target, DEVELOPMENT only.
This is a remaining-scaffold stress family, not a colored-core census repeat.
"""
from scaffold_hard_plant import *


def run_pairs(all_shapes=False):
    start=time.perf_counter();local=json.loads((ROOT/'results/algorithm-universal233-hard-plant-local-v1.json').read_text());c,x,y=6,7,8
    Aall=[ar for ar in trees(tuple(range(4))) if min(e['cost'] for e in generate(ar,{0:0,1:1,2:0,3:1})['cores'])>=2]
    assert len(Aall)==10
    if not all_shapes:Aall=[[[0,1],[2,3]]]
    ct={'A_topologies':len(Aall),'plant_patterns':0,'original_candidate_pairs':0,'earlier_admitted_pairs':0,'admitted_patterns':0,'vertices_checked':0,'selector_min_over_chain_bound':0,'selector_min_ge1':0};rows=[];worst=None;controls={}
    H=[[[0,2],4],[[1,3],5]]
    targetchain=Fraction(2929867400,2947295521)
    for ar in Aall:
      for mask in range(16):
        ct['plant_patterns']+=1;nextlabel=9;ts={};ss={}
        for k in range(4):
          if mask&(1<<k):
            mp=dict(zip(range(6),[k,*range(nextlabel,nextlabel+5)]));nextlabel+=5;ts[k]=relabel(local['T'],mp);ss[k]=relabel(local['Tprime'],mp)
        h=substitute(H,ts);a=substitute(ar,ss);admitted=[]
        for sr in source_six(a,[4,5],c,x,y):
          for tr in [[[c,h],[x,y]],[c,[[x,y],h]]]:
            ct['original_candidate_pairs']+=1
            if selected_valid(tr,sr,[x,y]):ct['earlier_admitted_pairs']+=1;admitted.append((tr,sr))
        if not admitted:
          if repr(ar)==repr([[0,1],[2,3]]) and mask==0:controls['empty_crossed_pattern_excluded']=True
          continue
        ct['admitted_patterns']+=1;tr,sr=admitted[0];w=scan_child(tr,sr,[x,y]);assert w is not None;o=run_vertex(w);ct['vertices_checked']+=len(o['vertex_rows']);score=Fraction(o['minimum_one_paid_full_mass'])
        ct['selector_min_over_chain_bound']+=score>targetchain;ct['selector_min_ge1']+=score>=1
        row={'source_A':ar,'plant_mask':mask,'admitted_contexts':len(admitted),'labels':nextlabel,'best_paid_mass':str(score),'raw_mass':o['minimum_raw_full_mass'],'full_paid_vectors':[]}
        for vr in o['vertex_rows']:
          vec=[1,1]
          for em in vr['emissions']:
            cr=em['continuation']
            if cr['kind']=='exact_depth1':continue
            ds=cr['decreases'] if cr['kind']=='one_actual_vertex_split' else cr['other_parent_lower_bound_losses'];vec +=[2+em['cost']+d for d in ds]
          row['full_paid_vectors'].append(sorted(vec))
        rows.append(row)
        if worst is None or score>Fraction(worst['score']):worst={'score':str(score),'row':row,'literal':o}
        if repr(ar)==repr([[0,1],[2,3]]) and mask==5:
          assert sorted(row['full_paid_vectors'][0])==[1,1,3,4,6,6];controls['nineteen_label_paid_vector_reproduced']=True
    assert all(controls.values())
    return {'counts':ct,'control_results':controls,'rows':rows,'worst':worst,'elapsed_seconds':time.perf_counter()-start,'scope':'Finite targeted development X0; NO-FIRE is not universal coverage/charging proof'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--all-shapes',action='store_true');p.add_argument('--out',required=True);a=p.parse_args();ctls=controls();o=run_pairs(a.all_shapes)
    out={'controls':ctls,'search':o,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((HERE/'PAIR-CHARGING-X0-PIN-v1.json').read_bytes()).hexdigest()};Path(a.out).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in o.items() if k not in ['rows','worst']}));print('Worst min paid mass',o['worst']['score'] if o['worst'] else 'none')
