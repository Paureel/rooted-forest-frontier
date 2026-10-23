"""One-shot common-cluster-free extension; frozen14 files remain immutable."""
from pathlib import Path
import sys,json,time,hashlib
D=Path(__file__).resolve().parent;sys.path.insert(0,str(D.parent))
from scaffold_vertex_replay import *

if __name__=='__main__':
    start=time.perf_counter();ctls=controls();base=json.loads((ROOT/'results/algorithm-universal233-pair-charging-fire-v1.json').read_text())['witness'];t,s,ch=base['original_T'],base['original_Tprime'],base['cherry'];st=Tree(s);Dlabels={3,9,10,11,12,13};moving=1
    assert selected_valid(t,s,ch) and Fraction(base['minimum_one_paid_full_mass'])>1
    stripped=Tree(t).restriction(Tree(t).labels-{moving});tt=Tree(stripped);places=[p for p,ls in tt.below.items() if ls<=Dlabels];rootD=next(p for p,ls in tt.below.items() if ls==Dlabels)
    clean=graft(stripped,tuple(map(int,rootD)),moving);assert Tree(clean).clusters(st.labels)==Tree(t).clusters(st.labels) and selected_valid(clean,s,ch)
    oldparts={key for vr in base['vertex_rows'] for e in vr['emissions'] for key in [json.dumps({'source':e['source'],'cuts':e['cuts'],'partition':e['partition']},sort_keys=True)]}
    counts={'target_reattachments':0,'selected_and_earlier_admitted':0,'no_proper_common_clusters':0,'all_selector_paid_mass_ge1':0};rows=[];fire=None
    for p in places:
      nt=graft(stripped,tuple(map(int,p)),moving);counts['target_reattachments']+=1
      if not selected_valid(nt,s,ch):continue
      counts['selected_and_earlier_admitted']+=1;common=(Tree(nt).clusters(st.labels)&st.clusters(st.labels))-{st.labels};row={'target_attachment_address':p,'proper_common_clusters':[sorted(x) for x in common]}
      if common:rows.append(row);continue
      counts['no_proper_common_clusters']+=1;w=scan_child(nt,s,ch);assert w is not None;o=run_vertex(w)
      # Same source, same concrete source-core certificate; color renaming may
      # reverse output orders, so compare source/cut/partition record sets.
      for vr in o['vertex_rows']:
        assert vr['region_counts']==[2,2]
        for e in vr['emissions']:
          assert json.dumps({'source':e['source'],'cuts':e['cuts'],'partition':e['partition']},sort_keys=True) in oldparts
      row['minimum_paid_full_mass']=o['minimum_one_paid_full_mass'];row['literal']=o
      if Fraction(o['minimum_one_paid_full_mass'])>=1:counts['all_selector_paid_mass_ge1']+=1;fire=fire or row
      rows.append(row)
    out={'controls':ctls,'clean_target_reconstruction':True,'counts':counts,'rows':rows,'first_fire':fire,'elapsed_seconds':time.perf_counter()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((D/'PIN-v1.json').read_bytes()).hexdigest(),'scope':'Finite exact extension. No frozen14 checkpoint writes; no complete algorithm or runtime lower-bound claim.'};(ROOT/'results/algorithm-universal233-pair-clusterfree-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['controls','rows','first_fire']}));print('Fire',None if fire is None else fire['minimum_paid_full_mass'])
