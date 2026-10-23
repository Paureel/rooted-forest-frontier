"""One-shot family extension of cherry selector wrappers; DEVELOPMENT only.
The toolkit has no MAF selector engine. Reuse exact frozen source predicates,
source-core and local scheduler, with explicit contacts in the accompanying pin.
"""
from pathlib import Path
import sys,json,time,hashlib,argparse
D=Path(__file__).resolve().parent;sys.path.insert(0,str(D.parent))
from scaffold_hard_plant import *
from scaffold_vertex_replay import run_vertex,paid_next


def inspect(t,s):
    c=Fraction(233,100);rows=[]
    for orientation,(raw,source) in enumerate([(t,s),(s,t)]):
        tt,st=Tree(raw),Tree(source);ap=applicability(tt,st);assert ap['excluded_2a_to_2d']
        assert sorted(tuple(x['cherry']) for x in ap['rows'])==sorted(tuple(x) for x in tt.cherries())
        for ar in ap['rows']:
            assert ar['t']==2
            bs,empty=st.cut_blocks([p['edge'] for p in ar['pendants']]);assert not empty
            red=tidy(raw,[st.restriction(b) for b in bs]);cl=classify(red['T'],red['forest_trees']);pairs=cl['overlap_pairs']
            row={'orientation':orientation,'cherry':ar['cherry'],'overlap_pairs':pairs,'homeomorphic':cl['homeomorphic'],'live_parents':len(red['forest_trees'])}
            if not pairs:
                mass,cr=paid_next(red['T'],red['forest_trees'],c);row['full_mass']=str(2/c+mass/c**2);row['scheduler']=cr
            elif len(pairs)==1:
                o=run_vertex({'original_T':raw,'original_Tprime':source,'cherry':ar['cherry'],'reduced':red});row['full_mass']=o['minimum_one_paid_full_mass'];row['vertices']=[{'v':v['vertex'],'regions':v['region_counts'],'full_mass':v['after_one_paid_continuation_full_mass']} for v in o['vertex_rows']]
            elif len(red['forest_trees'])==3 and len(pairs) in [2,3]:row['full_mass']='CONDITIONAL-JOINT geometry'
            else:row['full_mass']='UNSCORED geometry'
            rows.append(row)
    return rows


def main(limit,out):
    start=time.perf_counter();ctls=controls();old=json.loads((ROOT/'results/algorithm-universal233-pair-charging-x0-v2.json').read_text())['search']['rows'];assert len(old)==98
    known=json.loads((ROOT/'results/algorithm-universal233-pair-charging-fire-v1.json').read_text())['witness'];probe=inspect(known['original_T'],known['original_Tprime'])
    assert next(r for r in probe if r['orientation']==0 and r['cherry']==[7,8])['full_mass']=='2962867400/2947295521'
    assert next(r for r in probe if r['orientation']==0 and r['cherry']==[0,2])['full_mass']=='2729867400/2947295521'
    local=json.loads((ROOT/'results/algorithm-universal233-hard-plant-local-v1.json').read_text());H=[[[0,2],4],[[1,3],5]];rows=[];first=None
    count={'patterns':0,'hard_cherries':0,'actual_passing_choice':0,'conditional_joint_only':0,'fire':0}
    for pat in old[:limit]:
        tick=time.perf_counter();ts={};ss={};nxt=9
        for k in range(4):
            if pat['plant_mask']&(1<<k):
                mp=dict(zip(range(6),[k,*range(nxt,nxt+5)]));nxt+=5;ts[k]=relabel(local['T'],mp);ss[k]=relabel(local['Tprime'],mp)
        h=substitute(H,ts);a=substitute(pat['source_A'],ss);ad=None
        for sr in source_six(a,[4,5],6,7,8):
            for tr in [[[6,h],[7,8]],[6,[[7,8],h]]]:
                if selected_valid(tr,sr,[7,8]):ad=(tr,sr);break
            if ad is not None:break
        assert ad is not None
        choices=inspect(*ad);actual=[r for r in choices if r['full_mass'] not in ['CONDITIONAL-JOINT geometry','UNSCORED geometry'] and Fraction(r['full_mass'])<1];conditional=any(r['full_mass']=='CONDITIONAL-JOINT geometry' for r in choices)
        count['patterns']+=1;count['hard_cherries']+=len(choices);count['actual_passing_choice']+=bool(actual);count['conditional_joint_only']+=not actual and conditional;count['fire']+=not actual and not conditional
        row={'source_A':pat['source_A'],'plant_mask':pat['plant_mask'],'labels':nxt,'original_selected_score':pat['best_paid_mass'],'choices':choices,'actual_passes':len(actual),'conditional_joint_alternative':conditional,'seconds':time.perf_counter()-tick};rows.append(row)
        if not actual and not conditional and first is None:first={'original_T':ad[0],'original_Tprime':ad[1],'row':row}
    record={'controls':ctls,'selector_controls':{'frozen14_selected_mass':True,'frozen14_alternative_disjoint_mass':True,'all_cherries_once':True},'limit':limit,'counts':count,'rows':rows,'first_fire':first,'elapsed_seconds':time.perf_counter()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((D/'FAMILY-PIN-v1.json').read_bytes()).hexdigest(),'scope':'Finite development source family; universal selectable bound and charged implementation OPEN.'};Path(out).write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:v for k,v in record.items() if k not in ['rows','first_fire','controls']}))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--limit',type=int,required=True);p.add_argument('--out',required=True);a=p.parse_args();main(a.limit,a.out)
