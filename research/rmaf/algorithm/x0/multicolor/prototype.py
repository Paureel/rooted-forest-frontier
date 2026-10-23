"""One-shot multicolor-core falsifier prototype, not a production generator.

This module imports no reference oracle. It implements the pinned recursive
operations directly and returns original source cuts and lifted label groups.
No optimum, agreement-forest or partition-enumeration oracle is used here.
"""
from collections import Counter
from dataclasses import dataclass


@dataclass(frozen=True)
class Node:
    address: str
    group: tuple | None = None
    children: tuple | None = None


def read_source(raw, colors):
    seen=set()
    def build(x, address):
        if isinstance(x,int) and not isinstance(x,bool):
            if x in seen:
                raise ValueError('duplicate source label')
            seen.add(x)
            return Node(address,(x,),None)
        if not isinstance(x,(list,tuple)) or len(x)!=2:
            raise ValueError('nonbinary source')
        return Node(address,None,(build(x[0],address+'0'),build(x[1],address+'1')))
    tree=None if raw is None else build(raw,'')
    if set(colors)!=seen:
        raise ValueError('missing or foreign color label')
    if any(not isinstance(c,int) or isinstance(c,bool) or c<0 for c in colors.values()):
        raise ValueError('colors must be nonnegative integers')
    return tree


def groups(tree):
    if tree is None:
        return []
    if tree.group is not None:
        return [tree]
    return groups(tree.children[0])+groups(tree.children[1])


def normalize(tree, colors):
    if tree is None or tree.group is not None:
        return tree,[]
    left,log_l=normalize(tree.children[0],colors)
    right,log_r=normalize(tree.children[1],colors)
    history=log_l+log_r
    if left.group is not None and right.group is not None and colors[left.group[0]]==colors[right.group[0]]:
        merged=tuple(sorted(left.group+right.group))
        history.append({'operation':'homogeneous_cherry_contract','original_node':tree.address,
                        'children':[left.address,right.address],'groups':[list(left.group),list(right.group)],
                        'lifted_group':list(merged)})
        return Node(tree.address,merged,None),history
    return Node(tree.address,None,(left,right)),history


def mixed_cherry(tree):
    if tree.group is not None:
        return None
    left,right=tree.children
    if left.group is not None and right.group is not None:
        return left,right
    return mixed_cherry(left) or mixed_cherry(right)


def delete_group(tree, address):
    """Delete a current leaf group and suppress unary nodes, keeping source IDs."""
    if tree.address==address:
        return None,[]
    if tree.group is not None:
        return tree,[]
    left,log_l=delete_group(tree.children[0],address)
    right,log_r=delete_group(tree.children[1],address)
    history=log_l+log_r
    if left is None or right is None:
        survivor=left or right
        history.append({'operation':'unary_suppress','original_node':tree.address,
                        'replacement_original_node':survivor.address,
                        'was_root':tree.address==''})
        return survivor,history
    return Node(tree.address,None,(left,right)),history


def key(partition):
    return tuple(sorted(tuple(sorted(b)) for b in partition))


def generate(raw, colors, budget=None, omit_first_mixed_right=False):
    if budget is not None and (not isinstance(budget,int) or isinstance(budget,bool) or budget<0):
        raise ValueError('budget must be nonnegative integer')
    tree=read_source(raw,colors)
    stats={'nodes_visited':0,'normalized_contractions':0,'cut_children_attempted':0,
           'budget_pruned_prefixes':0,'mixed_branch_pairs':0,'omitted_branches':0,
           'raw_emissions':0,'duplicate_emissions_removed':0}
    emitted=[]
    def run(current,detached,cuts,events,mixed_seen):
        stats['nodes_visited']+=1
        current,contractions=normalize(current,colors)
        stats['normalized_contractions']+=len(contractions)
        events=events+contractions
        leaves=groups(current)
        used={colors[g.group[0]] for g in leaves}
        if not leaves:
            partition=[]
            emitted.append({'partition':partition,'cuts':list(cuts),'cost':len(cuts),'events':events})
            return
        if len(used)==1:
            remaining=sorted(x for g in leaves for x in g.group)
            partition=[list(g) for g in detached]+[remaining]
            partition.sort(key=lambda b:min(b))
            emitted.append({'partition':partition,'cuts':list(cuts),'cost':len(cuts),'events':events})
            return
        counts=Counter(colors[g.group[0]] for g in leaves)
        unique=sorted(c for c,count in counts.items() if count==1)
        if unique:
            c=unique[0]
            selected=[next(g for g in leaves if colors[g.group[0]]==c)]
            mode='unique_color_detach'
            next_seen=mixed_seen
        else:
            pair=mixed_cherry(current)
            if pair is None:
                raise AssertionError('no mixed cherry in normalized multicolor source')
            selected=list(pair)
            mode='mixed_cherry_detach'
            stats['mixed_branch_pairs']+=1
            next_seen=mixed_seen+1
            if omit_first_mixed_right and mixed_seen==0:
                selected=selected[:1]
                stats['omitted_branches']+=1
        for chosen in selected:
            stats['cut_children_attempted']+=1
            if chosen.address=='':
                raise AssertionError('attempt to detach root group')
            edge=[chosen.address[:-1],chosen.address]
            if edge in cuts:
                raise AssertionError('repeated original source cut')
            if budget is not None and len(cuts)+1>budget:
                stats['budget_pruned_prefixes']+=1
                continue
            remaining,suppression=delete_group(current,chosen.address)
            event={'operation':mode,'original_edge':edge,'detached_labels':list(chosen.group),
                   'color':colors[chosen.group[0]],'paid_cost':1}
            run(remaining,detached+[chosen.group],cuts+[edge],events+[event]+suppression,next_seen)
    run(tree,[],[],[],0)
    stats['raw_emissions']=len(emitted)
    dedup={}
    for e in emitted:
        k=key(e['partition'])
        if k in dedup:
            stats['duplicate_emissions_removed']+=1
        else:
            dedup[k]=e
    result=list(dedup.values())
    result.sort(key=lambda e:key(e['partition']))
    return {'cores':result,'raw_cores':emitted,'stats':stats,
            'budget':budget,'used_colors':len(set(colors.values()))}
