"""One-shot hard-cherry selector probe wrapping existing MAF instruments.
BootLoops index lacks MAF selection tools; use frozen source/vertex instruments
as documented DEVELOPMENT contacts. Not independent verification or a solver.
"""
from pathlib import Path
import sys,json,time,hashlib
D=Path(__file__).resolve().parent;sys.path.insert(0,str(D.parent))
from scaffold_vertex_replay import *

def inspect(t,s):
    allrows=[]
    for orientation,(raw,source) in enumerate([(t,s),(s,t)]):
        tt,st=Tree(raw),Tree(source);app=applicability(tt,st)
        assert app['excluded_2a_to_2d']
        assert sorted(tuple(r['cherry']) for r in app['rows'])==sorted(tuple(c) for c in tt.cherries())
        for ar in app['rows']:
            assert ar['t']==2
            blocks,empty=st.cut_blocks([p['edge'] for p in ar['pendants']]);assert not empty
            red=tidy(raw,[st.restriction(b) for b in blocks]);cl=classify(red['T'],red['forest_trees'])
            row={'orientation':orientation,'cherry':ar['cherry'],'paid_source_edges':[p['edge'] for p in ar['pendants']],'reduced':red,'classification':cl,'pair_score':'UNSCORED geometry'}
            old=scan_child(raw,source,ar['cherry'])
            if old is not None:
                score=run_vertex(old)
                row['pair_score']=score['minimum_one_paid_full_mass'];row['vertex_counts']=[v['region_counts'] for v in score['vertex_rows']]
            allrows.append(row)
    return allrows

if __name__=='__main__':
    start=time.perf_counter();ctls=controls()
    base=json.loads((ROOT/'results/algorithm-universal233-pair-charging-fire-v1.json').read_text())['witness']
    cf=json.loads((ROOT/'results/algorithm-universal233-pair-clusterfree-v1.json').read_text())['first_fire']['literal']
    rows=[]
    for name,w in [('frozen14',base),('clusterfree14',cf)]:
        t0=time.perf_counter();r=inspect(w['original_T'],w['original_Tprime'])
        known=[x for x in r if x['orientation']==0 and x['cherry']==[7,8]];assert len(known)==1 and known[0]['pair_score']=='2962867400/2947295521'
        assert not any(x['orientation']==0 and x['cherry']==[0,1] for x in r)
        rows.append({'name':name,'rows':r,'seconds':time.perf_counter()-t0})
    out={'controls':ctls,'enumeration_controls':{'selected_known_mass':True,'noncherry_absent':True,'all_target_cherries_once_per_orientation':True},'states':rows,'elapsed_seconds':time.perf_counter()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((D/'PIN-v1.json').read_bytes()).hexdigest(),'scope':'Finite exact selector probe. UNSCORED geometries remain unscored; no universal algorithm/runtime conclusion.'}
    (ROOT/'results/algorithm-universal233-cherry-selection-v1.json').write_text(json.dumps(out,indent=2)+'\n')
    for s in rows:
        print(s['name'],s['seconds'])
        for r in s['rows']:print(r['orientation'],r['cherry'],r['classification']['overlap_pairs'],r['classification']['homeomorphic'],r['pair_score'])
