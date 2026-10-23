"""One-shot extension of the exact all-hard-cherry table, with paid scheduling.
No new core/search engine: extend v1 wrapper, preserving its original receipt.
"""
from pathlib import Path
import importlib.util,json,time,hashlib
D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('cherry_selector_v1',D/'check.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
Tree,ROOT,Fraction=m.Tree,m.ROOT,m.Fraction
start=time.perf_counter();ctls=m.controls();base=json.loads((ROOT/'results/algorithm-universal233-cherry-selection-v1.json').read_text());original=json.loads((ROOT/'results/algorithm-universal233-pair-charging-fire-v1.json').read_text())['witness'];cf=json.loads((ROOT/'results/algorithm-universal233-pair-clusterfree-v1.json').read_text())['first_fire']['literal'];c=Fraction(233,100)
for state,w in zip(base['states'],[original,cf]):
    for row in state['rows']:
        raw,source=(w['original_T'],w['original_Tprime']) if row['orientation']==0 else (w['original_Tprime'],w['original_T'])
        pairs=row['classification']['overlap_pairs'];r=row['reduced']
        if not pairs:
            mass,cont=m.paid_next(r['T'],r['forest_trees'],c);row['full_score']=str(2/c+mass/c**2);row['continuation']=cont
            if cont['kind']=='actual_disjoint_depth1_schedule' and sum(not x for x in row['classification']['homeomorphic'])>=2:
                assert all(x>=1 for x in cont['other_parent_lower_bound_losses'])
        elif len(pairs)==1:
            probe=m.run_vertex({'original_T':raw,'original_Tprime':source,'cherry':row['cherry'],'reduced':r});row['full_score']=probe['minimum_one_paid_full_mass'];row['all_vertex_scores']=[{'vertex':v['vertex'],'region_counts':v['region_counts'],'full_score':v['after_one_paid_continuation_full_mass']} for v in probe['vertex_rows']]
        else:row['full_score']='UNSCORED geometry'
    known=next(x for x in state['rows'] if x['orientation']==0 and x['cherry']==[7,8]);assert known['full_score']=='2962867400/2947295521'
    scored=[r for r in state['rows'] if r['full_score']!='UNSCORED geometry'];state['best']=min(scored,key=lambda r:Fraction(r['full_score']));state['passing_choices']=sum(Fraction(r['full_score'])<1 for r in scored)
out={'controls':ctls,'states':base['states'],'elapsed_seconds':time.perf_counter()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((D/'PIN-v2.json').read_bytes()).hexdigest(),'scope':'Exact finite selector repair only; each actual local task budget charged. No universal existence/proof of global algorithm.'};(ROOT/'results/algorithm-universal233-cherry-selection-v2.json').write_text(json.dumps(out,indent=2)+'\n')
for s in out['states']:
 print(s['name'],'passing',s['passing_choices'])
 for r in s['rows']:print(r['orientation'],r['cherry'],r['full_score'],r.get('continuation',''))
