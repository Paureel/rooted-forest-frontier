#!/usr/bin/env python3
"""One-shot PRE-CANDIDATE instrument, authored from the permitted frozen spec.

No imports from author, old global checker, or other verifier code. Original
vertices use breadth-first integer IDs; addresses are separate identity data.
The current generator is an independently mutated pointer tree, not GTree.
"""
from collections import Counter, deque
from copy import deepcopy
from fractions import Fraction
from itertools import combinations


def syntax_leaves(tree):
    if type(tree) is int and tree >= 0:
        return [tree]
    if not isinstance(tree,(tuple,list)) or len(tree) != 2:
        raise ValueError('nonempty binary Nat tree required')
    return syntax_leaves(tree[0]) + syntax_leaves(tree[1])


class OriginalGraph:
    def __init__(self,tree):
        self.labels = syntax_leaves(tree)
        self.address = {}
        self.at = {}
        self.parent = {}
        self.children = {}
        self.leaf = {}
        self.adj = {}
        pending = deque([(tree,(),None)])
        while pending:
            subtree,where,parent = pending.popleft()
            vertex = len(self.address)
            self.address[vertex] = where
            self.at[where] = vertex
            self.parent[vertex] = parent
            self.adj[vertex] = set()
            if parent is not None:
                self.adj[parent].add(vertex)
                self.adj[vertex].add(parent)
                self.children[parent].append(vertex)
            if type(subtree) is int:
                self.leaf[vertex] = subtree
            else:
                self.children[vertex] = []
                pending.append((subtree[0],where+(0,),vertex))
                pending.append((subtree[1],where+(1,),vertex))

    def edge(self,address):
        address = tuple(address)
        if not address or any(type(x) is not int or x not in (0,1) for x in address):
            raise ValueError('not an original nonroot edge address')
        if address not in self.at:
            raise ValueError('not an original vertex')
        v = self.at[address]
        return self.parent[v],v

    def path(self,start,end):
        queue = deque([start])
        previous = {start:None}
        while queue:
            v = queue.popleft()
            if v == end:
                result=[]
                while v is not None:
                    result.append(v)
                    v=previous[v]
                return list(reversed(result))
            for w in sorted(self.adj[v]):
                if w not in previous:
                    previous[w]=v
                    queue.append(w)
        raise AssertionError('original graph is disconnected')

    def span(self,labels):
        nodes=[]
        for label in labels:
            matches=[v for v,x in self.leaf.items() if x==label]
            if len(matches)!=1:
                raise ValueError('label is absent or not distinct')
            nodes.append(matches[0])
        if not nodes:
            return set()
        return {nodes[0]}.union(*(set(self.path(nodes[0],v)) for v in nodes[1:]))

    def residual(self,cuts):
        cuts=[tuple(a) for a in cuts]
        if len(set(cuts))!=len(cuts):
            raise ValueError('duplicate original edge')
        removed={frozenset(self.edge(a)) for a in cuts}
        unvisited=set(self.address)
        parts=[]
        while unvisited:
            seed=min(unvisited)
            queue=deque([seed])
            unvisited.remove(seed)
            vertices=[]
            while queue:
                v=queue.popleft()
                vertices.append(v)
                for w in sorted(self.adj[v]):
                    if w in unvisited and frozenset((v,w)) not in removed:
                        unvisited.remove(w)
                        queue.append(w)
            labels=sorted(self.leaf[v] for v in vertices if v in self.leaf)
            parts.append({'vertices':sorted(vertices),'addresses':[list(self.address[v]) for v in sorted(vertices)],'labels':labels})
        return {'components':parts,'leaf_partition':sorted(p['labels'] for p in parts if p['labels']),
                'nonempty':all(p['labels'] for p in parts),'count':len(parts),
                'cuts_plus_one':len(parts)==len(cuts)+1,'cuts':len(cuts)}


def proper_labels(labels,n):
    return type(n) is int and n>=0 and all(type(x) is int and x>=0 for x in labels) and sorted(labels)==list(range(n))


def proper_partition(graph,blocks):
    return (len(set(graph.labels))==len(graph.labels) and all(blocks) and
            Counter(x for b in blocks for x in b)==Counter(graph.labels))


def convex_partition(graph,blocks):
    if not proper_partition(graph,blocks):
        return False
    spans=[graph.span(b) for b in blocks]
    return all(not spans[i]&spans[j] for i in range(len(spans)) for j in range(i))


def monochromatic(blocks,colors):
    return all(b and len({colors[x] for x in b})==1 for b in blocks)


def refines(fine,coarse):
    return all(any(set(b)<=set(a) for a in coarse) for b in fine)


def canonical(blocks):
    return sorted(sorted(b) for b in blocks)


def _leaf_order(state):
    out=[]
    stack=[state['root']]
    while stack:
        v=stack.pop()
        if v in state['groups']:
            out.append(v)
        else:
            left,right=state['children'][v]
            stack.extend((right,left))
    return out


def _normalize(state):
    order=[]
    todo=[(state['root'],False)]
    while todo:
        v,seen=todo.pop()
        if v in state['groups']:
            continue
        if seen:
            order.append(v)
        else:
            todo.append((v,True))
            left,right=state['children'][v]
            todo.extend(((right,False),(left,False)))
    for v in order:
        left,right=state['children'][v]
        if left in state['groups'] and right in state['groups']:
            a,b=state['groups'][left],state['groups'][right]
            if a[1]==b[1]:
                state['groups'][v]=(a[0]+b[0],a[1])
                del state['groups'][left]
                del state['groups'][right]
                del state['children'][v]


def _erase_group(state,group):
    if group==state['root']:
        return None,None
    parents={child:parent for parent,pair in state['children'].items() for child in pair}
    parent=parents[group]
    other=next(v for v in state['children'][parent] if v!=group)
    del state['groups'][group]
    del state['children'][parent]
    if parent==state['root']:
        state['root']=other
    else:
        upper=parents[parent]
        state['children'][upper]=[other if v==parent else v for v in state['children'][upper]]
    return state,parent


def generate(tree,colors,q):
    labels=syntax_leaves(tree)
    if type(q) is not int or q<0:
        raise ValueError('Nat budget required')
    if len(set(labels))!=len(labels):
        return {'outputs':[],'refusals':['duplicate original label'],'visited':0,'attempts':0,'pruned':0,'trace':[]}
    if any(x not in colors or type(colors[x]) is not int or colors[x]<0 for x in labels):
        raise ValueError('Nat color required at every actual label')
    graph=OriginalGraph(tree)
    initial={'root':0,'children':deepcopy(graph.children),
             'groups':{v:((x,),colors[x]) for v,x in graph.leaf.items()}}
    def recurse(state,detached,cuts,left):
        _normalize(state)
        order=_leaf_order(state)
        color_counts=Counter(state['groups'][v][1] for v in order)
        result={'outputs':[],'refusals':[],'visited':1,'attempts':0,'pruned':0,'trace':[]}
        if len(color_counts)==1:
            remaining=[x for v in order for x in state['groups'][v][0]]
            result['outputs']=[{'partition':[list(g) for g in detached]+[remaining],
                                'cuts':[list(a) for a in cuts]}]
            return result
        unique=next((v for v in order if color_counts[state['groups'][v][1]]==1),None)
        if unique is not None:
            choices=[unique]
        else:
            stack=[state['root']]
            choices=None
            while stack:
                v=stack.pop()
                if v in state['groups']:
                    continue
                a,b=state['children'][v]
                if a in state['groups'] and b in state['groups']:
                    if state['groups'][a][1]==state['groups'][b][1]:
                        raise AssertionError('uncontracted homogeneous cherry')
                    choices=[a,b]
                    break
                stack.extend((b,a))
            if choices is None:
                result['refusals'].append('no mixed cherry')
                return result
        for group in choices:
            result['attempts']+=1
            where=graph.address[group]
            if not where or where in cuts:
                result['refusals'].append('root or duplicate original edge')
                continue
            group_labels=state['groups'][group][0]
            branch,parent=_erase_group(deepcopy(state),group)
            if branch is None:
                result['refusals'].append('entire current source removed')
                continue
            event={'chosen':list(where),'current_parent':list(graph.address[parent]),
                   'original_parent':list(where[:-1]),
                   'original_path':[list(graph.address[v]) for v in graph.path(parent,group)],
                   'pruned':left==0}
            result['trace'].append(event)
            if left==0:
                result['pruned']+=1
                continue
            child=recurse(branch,[group_labels]+detached,[where]+cuts,left-1)
            for key in ('outputs','refusals','trace'):
                result[key]+=child[key]
            for key in ('visited','attempts','pruned'):
                result[key]+=child[key]
        return result
    return recurse(initial,[],[],min(q,len(labels)-1))


def validate_emission(tree,colors,q,out):
    try:
        graph=OriginalGraph(tree)
        residual=graph.residual(out['cuts'])
        blocks=out['partition']
        return (len(out['cuts'])<=q and residual['nonempty'] and residual['cuts_plus_one'] and
                len(out['cuts'])+1==len(blocks) and
                canonical(blocks)==residual['leaf_partition'] and
                proper_partition(graph,blocks) and monochromatic(blocks,colors))
    except (KeyError,ValueError,TypeError):
        return False


def raw_mass(outputs,base):
    if not isinstance(base,(Fraction,int)) or type(base) is bool:
        raise ValueError('exact rational mass base required')
    base=Fraction(base)
    if base<=1:
        raise ValueError('mass base must exceed one')
    return sum((base**(-len(o['cuts'])) for o in outputs),Fraction(0))


def named_source_audit(text):
    import re
    forbidden=re.findall(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s+\w+',text,re.M)
    return not forbidden


def origin_matches(registry,observed):
    return registry==observed
