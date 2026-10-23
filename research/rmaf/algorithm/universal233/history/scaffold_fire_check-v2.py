"""One-shot original-source lift checker for the14-label paid pair refuter.
Uses explicit original cut components, not optimal partitions or cut-subset
containment. Source predicates/oracle are declared DEVELOPMENT contacts.
"""
from scaffold_vertex_replay import *


def key(p):return sorted(sorted(b) for b in p)

def lean_tree(t):return f'(.leaf {t})' if isinstance(t,int) else f'(.node {lean_tree(t[0])} {lean_tree(t[1])})'

def lean_list(xs):return '['+', '.join(lean_list(x) if isinstance(x,list) else str(x) for x in xs)+']'

if __name__=='__main__':
    ctls=controls();p=ROOT/'results/algorithm-universal233-pair-charging-fire-v1.json';o=json.loads(p.read_text());w=o['witness'];t,s=Tree(w['original_T']),Tree(w['original_Tprime']);ch=w['cherry'];assert selected_valid(t.raw,s.raw,ch)
    ps=s.pendant(*ch);hardcuts=[tuple(z['edge']) for z in ps];base,empty=s.cut_blocks(hardcuts);assert not empty
    red=w['reduced'];F=[Tree(ft) for ft in red['forest_trees']];expand={int(k):v for k,v in red['expansion'].items()}
    parents=[sorted(x for a in f.labels for x in expand[a]) for f in F];assert key(parents)==key(base)
    cl=classify(red['T'],red['forest_trees']);assert cl['homeomorphic']==[False,True,True] and cl['overlap_pairs']==[[0,1]]
    rt=Tree(red['T']);shared=rt.span(F[0].labels)&rt.span(F[1].labels);sharededges=[e for e in rt.edges if set(e)<=shared];assert len(shared)==3 and len(sharededges)==2
    # No eligible isolated homeomorphic group of size>=2 (source rule7).
    goods=[i for i,h in enumerate(cl['homeomorphic']) if h];rule7=[]
    for n in range(2,len(goods)+1):
      for group in combinations(goods,n):
        if not any(i in group and j not in group or j in group and i not in group for i,j in cl['overlap_pairs']):rule7.append(group)
    assert not rule7
    rows=[];qpartitions=[];caught=[]
    for vr in w['vertex_rows']:
      assert vr['region_counts']==[2,2];vec=[1,1]
      for e in vr['emissions']:
        i=e['source'];f=F[i];corecuts=[tuple(x) for x in e['cuts']];blocks,empty=f.cut_blocks(corecuts)
        assert not empty and key(blocks)==key(e['partition']) and len(blocks)==len(corecuts)+1==e['cost']+1
        lifted=[]
        for _,v in corecuts:
          labels=set(x for a in f.below[v] for x in expand[a]);matches=[edge for edge in s.edges if set(s.below[edge[1]])==labels]
          assert len(matches)==1;lifted+=matches
        allcuts=hardcuts+lifted;actual,empty=s.cut_blocks(allcuts);expected=[]
        for j,ft in enumerate(F):
          bs=e['partition'] if j==i else [sorted(ft.labels)]
          expected +=[sorted(x for a in b for x in expand[a]) for b in bs]
        assert not empty and key(actual)==key(expected) and len(actual)==len(allcuts)+1
        assert validate_partition(s,s,actual)['valid']
        # Removing an actual core cut must change its claimed component partition.
        corrupt,_=s.cut_blocks(allcuts[:-1]);assert key(corrupt)!=key(actual);caught.append('omitted_original_core_cut')
        # Duplicating an edge cannot be counted as another component.
        dup,_=s.cut_blocks(allcuts+[allcuts[-1]]);assert len(dup)!=len(allcuts)+2;caught.append('duplicate_cut_charge')
        cr=e['continuation'];assert cr['kind']=='actual_disjoint_depth1_schedule' and cr['other_parent_lower_bound_losses']==[0]
        assert sum(x is None for x in cr['pretest_values'])==1 and all(x in [None,0] for x in cr['pretest_values'])
        vec.append(2+e['cost']);qpartitions.append(actual)
        rows.append({'vertex':vr['vertex'],'source':i,'original_cut_edges':allcuts,'expanded_partition':actual,'paid_additional':e['cost'],'local_query_losses':cr['other_parent_lower_bound_losses']})
      assert sorted(vec)==[1,1,3,4,4] and sum(Fraction(100,233)**d for d in vec)>1
    # Compact fixed Lean controls; no large-label optimum enumeration.
    unique={json.dumps(key(p)):key(p) for p in qpartitions};local=json.loads((ROOT/'results/algorithm-universal233-hard-plant-local-v1.json').read_text());parts=list(unique.values())
    lines=['import RMAF','namespace Universal233.ScaffoldWitness','open RMAF',f'def originalT : Tree := {lean_tree(t.raw)}',f'def originalS : Tree := {lean_tree(s.raw)}',f'def sourceParents : List (List Nat) := {lean_list(parents)}',f'def paidPartitions : List (List (List Nat)) := {lean_list(parts)}',f'def localT : Tree := {lean_tree(local["T"])}',f'def localS : Tree := {lean_tree(local["Tprime"])}',f'def localWitness : List (List Nat) := {lean_list(local["optimal_partitions"][0])}',
      'theorem properOriginalT : (leaves originalT).Nodup := by decide',
      'theorem properOriginalS : (leaves originalS).Nodup := by decide',
      'theorem sourceParentsPartition : partitionCheck (leaves originalS) sourceParents = true := by decide',
      'theorem sourceParentsDisjoint : pairwiseEmbeddings originalS sourceParents = true := by decide',
      'theorem paidSourceValid : paidPartitions.all (agreement originalS originalS) = true := by decide',
      'theorem paidTargetDisjoint : paidPartitions.all (pairwiseEmbeddings originalT) = true := by decide',
      'theorem exactlyOneBadParent : paidPartitions.all (fun bs => (bs.filter (fun b => !restrictionAgrees originalT originalS b)).length == 1) = true := by decide',
      'theorem localTwoCutsSuffice : agreement localT localS localWitness = true := by decide',
      'theorem localOneCutImpossible : (assignments 6 2).all (fun a => !(agreement localT localS (blocks a))) = true := by decide',
      'theorem oldMassFails : 233^4 < 2 * 233^3 * 100 + 233 * 100^3 + 2 * 100^4 := by decide']
    for name in ['properOriginalT','properOriginalS','sourceParentsPartition','sourceParentsDisjoint','paidSourceValid','paidTargetDisjoint','exactlyOneBadParent','localTwoCutsSuffice','localOneCutImpossible','oldMassFails']:lines.append('#print axioms '+name)
    lines.append('end Universal233.ScaffoldWitness');(HERE/'scaffold-proof/PairWitness.lean').write_text('\n'.join(lines)+'\n')
    (HERE/'scaffold-proof/FalsePairWitness.lean').write_text('import PairWitness\nnamespace Universal233.ScaffoldWitness\nopen RMAF\ntheorem falseOwnBudget : (0 : Nat) = 2 := by decide\ntheorem falseCompatible : paidPartitions.all (fun bs => (bs.filter (fun b => !restrictionAgrees originalT originalS b)).length == 0) = true := by decide\nend Universal233.ScaffoldWitness\n')
    record={'source_receipt':str(p),'source_receipt_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'source_parents':parents,'rows':rows,'unique_paid_partitions':parts,'original_earlier_priorities_absent_both_orientations':True,'source_rule6_inapplicable_two_overlap_edges':True,'source_rule7_no_isolated_good_group':True,'source_cut_lifts_all_nonredundant':True,'corruption_catches':caught,'scope':'Exact finite original cut realization and actual local-query score; no universal proof or improved algorithm claim','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (ROOT/'results/algorithm-universal233-pair-fire-original-cuts-v2.json').write_text(json.dumps(record,indent=2)+'\n');print('PASS original14-label source lifts:',len(rows),'finite core emissions;',len(caught),'deliberate cut-corruption catches;',len(parts),'unique paid partitions')
