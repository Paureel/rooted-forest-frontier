#!/usr/bin/env python3
"""One-shot source-envelope ledger, not a CPU model; standard library only.

No author work-package, proof code, or earlier verifier imports. Primitive
library/oracle contracts are declared in OPERATION-SPEC.md. Finite readiness
checks compare work as well as values and corrupt the returned event reports.
"""
import argparse
from collections import Counter
from copy import deepcopy
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from time import perf_counter

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]

def bits(x): return max(1, int(x).bit_length())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

@dataclass
class G:
    origin: str
    labels: object = None
    color: object = None
    left: object = None
    right: object = None

@dataclass
class Receipt:
    outputs: list
    refusals: list
    visited: int = 0
    attempts: int = 0
    pruned: int = 0

class Ledger:
    def __init__(self, data):
        self.events = []
        self.data = data
        self.max_nat_bits = 1

    def emit(self, kind, amount=1, sizes=None):
        self.events.append({'id':len(self.events), 'kind':kind, 'amount':amount,
                            'argument_sizes':sizes or []})

    def number(self, kind, a, b):
        width = max(bits(a),bits(b))
        self.max_nat_bits = max(self.max_nat_bits,width)
        self.emit(kind, sizes=[bits(a),bits(b)])
        return a == b

    def nat_demand(self,kind,values):
        widths = [bits(x) for x in values]
        self.max_nat_bits = max(self.max_nat_bits,*widths)
        self.emit(kind,sizes=widths)

    def add_counter(self,a,b):
        self.nat_demand('counter.add',[a,b])
        return a+b

    def append(self, domain, left, right):
        self.emit(f'append.{domain}.calls', sizes=[len(left),len(right)])
        self.emit(f'append.{domain}.left_cells',len(left),[len(left),len(right)])
        return left + right

    def origin_eq(self, a, b):
        self.emit('compare.origin',sizes=[len(a),len(b)])
        return a == b

    def raw_color(self,x):
        cfg = self.data.get('colors',{'kind':'id'})
        if cfg['kind'] == 'id': return x
        if cfg['kind'] == 'constant': return cfg['value']
        return cfg['values'][x]

    def color(self,x):
        self.emit('oracle.color_calls',sizes=[bits(x)])
        self.emit('oracle.tariff_units',self.data.get('oracle_tariff',1),[bits(x)])
        y = self.raw_color(x)
        self.max_nat_bits = max(self.max_nat_bits,bits(x),bits(y))
        return y

    def literal_current(self,tree,p=''):
        # Parsing a supplied stage input; deliberately not a generate charge.
        if isinstance(tree,int): return G(p,[tree],self.raw_color(tree))
        return G(p,left=self.literal_current(tree[0],p+'0'),right=self.literal_current(tree[1],p+'1'))

    def from_tree(self,tree,p=''):
        self.emit('fromTree.visit')
        if isinstance(tree,int): return G(p,[tree],self.color(tree))
        a = self.append('origin',p,'0'); b = self.append('origin',p,'1')
        return G(p,left=self.from_tree(tree[0],a),right=self.from_tree(tree[1],b))

    def leaves(self,tree):
        self.emit('leaves.visit')
        if isinstance(tree,int): return [tree]
        return self.append('leaves',self.leaves(tree[0]),self.leaves(tree[1]))

    def nodup(self,labels):
        self.emit('initial.nodup_calls')
        self.emit('initial.nodup_input_cells',len(labels))
        for i,x in enumerate(labels):
            for y in labels[i+1:]:
                if self.number('compare.label',x,y): return False
        return True

    def groups(self,t):
        self.emit('groups.visit')
        if t.labels is not None: return [t]
        return self.append('groups',self.groups(t.left),self.groups(t.right))

    def normalize(self,t):
        self.emit('normalize.visit')
        if t.labels is not None: return t
        a,b = self.normalize(t.left),self.normalize(t.right)
        if a.labels is not None and b.labels is not None:
            if self.number('compare.normalize_color',a.color,b.color):
                return G(t.origin,self.append('normalize_payload',a.labels,b.labels),a.color)
        return G(t.origin,left=a,right=b)

    def erase(self,chosen,t):
        self.emit('erase.visit')
        if self.origin_eq(t.origin,chosen): return None
        if t.labels is not None: return t
        a,b = self.erase(chosen,t.left),self.erase(chosen,t.right)
        if a is None: return b
        if b is None: return a
        return G(t.origin,left=a,right=b)

    def mixed(self,t):
        self.emit('mixedCherry.visit')
        if t.labels is not None: return None
        if t.left.labels is not None and t.right.labels is not None: return t.left,t.right
        a,b = self.mixed(t.left),self.mixed(t.right)  # declared eager envelope
        return a if a is not None else b

    def choose(self,t):
        self.emit('choose.calls')
        groups = self.groups(t)
        first = groups[0]
        uniform = True
        for g in groups:
            self.emit('choose.all_predicate')
            if not self.number('compare.choose_color',g.color,first.color):
                uniform = False; break
        if uniform: return 'finish',[]
        for g in groups:
            self.emit('choose.find_predicate')
            self.emit('choose.filter_calls')
            selected = []
            for h in groups:
                self.emit('choose.filter_predicate')
                if self.number('compare.filter_color',h.color,g.color):
                    self.emit('choose.filter_kept_cells'); selected.append(h)
            self.emit('length.filtered.calls'); self.emit('length.filtered.cells',len(selected))
            if self.number('compare.count',len(selected),1): return 'one',[g]
        pair = self.mixed(t)
        if pair is None: return 'refuse',['no mixed cherry in multicolor source']
        a,b = pair
        if self.number('compare.cherry_color',a.color,b.color):
            return 'refuse',['unnormalized homogeneous cherry']
        return 'two',[a,b]

    def combine(self,a,b):
        outputs = self.append('receipt_outputs',a.outputs,b.outputs)
        refusals = self.append('receipt_refusals',a.refusals,b.refusals)
        return Receipt(outputs,refusals,self.add_counter(a.visited,b.visited),
                       self.add_counter(a.attempts,b.attempts),self.add_counter(a.pruned,b.pruned))

    def prune(self,t,d,c):
        self.emit('prune.callback')
        return Receipt([],[],0,0,1)

    def attempt(self,continuation,t,d,c,g):
        self.emit('attempt.calls')
        if self.origin_eq(g.origin,''):
            self.emit('refusal.list_cells'); return Receipt([],['attempt to cut original root'],0,1,0)
        self.emit('cuts.contains_calls')
        for p in c:
            self.emit('cuts.contains_cells')
            if self.origin_eq(p,g.origin):
                self.emit('refusal.list_cells'); return Receipt([],['duplicate original source cut'],0,1,0)
        following = self.erase(g.origin,t)
        if following is None:
            self.emit('refusal.list_cells'); return Receipt([],['attempt removed entire current source'],0,1,0)
        self.emit('attempt.cons_cells',2)
        self.emit('attempt.continuation')
        r = continuation(following,[g]+d,[g.origin]+c)
        r.attempts = self.add_counter(r.attempts,1)
        return r

    def step(self,continuation,t,d,c):
        self.emit('step.calls')
        t = self.normalize(t)
        kind,chosen = self.choose(t)
        if kind == 'finish':
            self.emit('finish.map_cells',len(d))
            detached = [g.labels for g in d]
            groups = self.groups(t)
            labels = []
            for g in reversed(groups):
                self.emit('finish.flatmap_group_cells')
                labels = self.append('finish_payload',g.labels,labels)
            partition = self.append('finish_partition',detached,[labels])
            self.emit('finish.output_cells')
            return Receipt([{'partition':partition,'cuts':c[:]}],[],1,0,0)
        if kind == 'refuse':
            self.emit('refusal.list_cells'); return Receipt([],chosen,1,0,0)
        rows = [self.attempt(continuation,t,d,c,g) for g in chosen]
        r = rows[0] if kind == 'one' else self.combine(rows[0],rows[1])
        r.visited = self.add_counter(r.visited,1)
        return r

    def run(self,q,t,d,c):
        self.emit('run.calls',sizes=[bits(q)])
        if q == 0: return self.step(self.prune,t,d,c)
        self.nat_demand('budget.decrement',[q])
        return self.step(lambda u,e,f:self.run(q-1,u,e,f),t,d,c)

    def generate(self,tree,q):
        self.emit('generate.calls')
        if not self.nodup(self.leaves(tree)):
            self.emit('refusal.list_cells'); return Receipt([],['duplicate original label'])
        labels = self.leaves(tree)
        self.emit('length.initial.calls'); self.emit('length.initial.cells',len(labels))
        self.nat_demand('budget.subtract',[len(labels),1])
        self.nat_demand('budget.min',[q,max(0,len(labels)-1)])
        return self.run(min(q,max(0,len(labels)-1)),self.from_tree(tree),[],[])

def view(t):
    if t is None: return {'root':None,'groups':[]}
    groups,stack = [],[t]
    while stack:
        g = stack.pop()
        if g.labels is not None: groups.append([g.origin,g.labels,g.color])
        else: stack.extend([g.right,g.left])
    return {'root':t.origin,'groups':groups}

def rec_view(r):
    return {'outputs':r.outputs,'refusals':r.refusals,'visited':r.visited,'childAttempts':r.attempts,'pruned':r.pruned}

def raw_labels(tree):
    if isinstance(tree,int): return [tree]
    return raw_labels(tree[0])+raw_labels(tree[1])

def evaluate(case):
    d,op = case['input'],case['op']
    engine = Ledger(d)
    if op == 'append': value = engine.append(d['domain'],d['left'],d['right'])
    elif op == 'combine':
        def receipt(v): return Receipt(v['outputs'],v['refusals'],v.get('visited',0),v.get('attempts',0),v.get('pruned',0))
        value = rec_view(engine.combine(receipt(d['left']),receipt(d['right'])))
    elif op == 'fromTree': value = view(engine.from_tree(d['tree'],d.get('prefix','')))
    elif op == 'generate': value = rec_view(engine.generate(d['tree'],d['budget']))
    else:
        current = engine.literal_current(d['tree'],d.get('prefix',''))
        if d.get('normalize_input',False):
            setup = Ledger(d); current = setup.normalize(current)  # explicit supplied-stage setup
        if op == 'normalize': value = view(engine.normalize(current))
        elif op == 'groups': value = [[g.origin,g.labels,g.color] for g in engine.groups(current)]
        elif op == 'erase': value = view(engine.erase(d['chosen'],current))
        elif op == 'choose':
            kind,gs = engine.choose(current)
            value = {'kind':kind,'origins':[g.origin for g in gs]} if kind != 'refuse' else {'kind':kind,'refusals':gs}
        elif op == 'run': value = rec_view(engine.run(d['budget'],current,[],[]))
        elif op == 'attempt':
            group = G(d['group'][0],d['group'][1],d['group'][2])
            value = rec_view(engine.attempt(engine.prune,current,[],d.get('cuts',[]),group))
        else: raise ValueError(op)
    counts = dict(Counter())
    for event in engine.events: counts[event['kind']] = counts.get(event['kind'],0)+event['amount']
    labels = raw_labels(d['tree']) if 'tree' in d else []
    metadata = {'input_label_max_bits':max([bits(x) for x in labels] or [1]),
                'input_budget_bits':bits(d.get('budget',0)),
                'max_nat_operand_bits':engine.max_nat_bits,
                'oracle_tariff':d.get('oracle_tariff',1),
                'unit':'declared structural source-envelope operations, not machine cycles'}
    return {'value':value,'events':engine.events,'counts':counts,'metadata':metadata}

def validate(report,case):
    problems = []
    events = report['events']
    if [e['id'] for e in events] != list(range(len(events))): problems.append('duplicate/missing/noncontiguous event ID')
    recomputed = {}
    for e in events:
        if not isinstance(e['amount'],int) or e['amount'] < 0: problems.append('invalid event amount')
        recomputed[e['kind']] = recomputed.get(e['kind'],0)+e['amount']
    if recomputed != report['counts']: problems.append('exported counters differ from event records')
    for key,value in case.get('value_fields',{}).items():
        actual = report['value'] if key == '$' else report['value'][key]
        if actual != value: problems.append('value:'+key)
    for key,value in case['counts'].items():
        if report['counts'].get(key,0) != value: problems.append('work:'+key)
    for key,value in case.get('metadata',{}).items():
        if report['metadata'][key] != value: problems.append('encoding/oracle:'+key)
    return problems

def corrupt(report,plant):
    r = deepcopy(report)
    kind = plant['kind']
    if kind in ['zero_kind','omit_kind']:
        target = plant['target']
        if kind == 'zero_kind':
            for event in r['events']:
                if event['kind'] == target: event['amount'] = 0
        else: r['events'] = [e for e in r['events'] if e['kind'] != target]
        for i,event in enumerate(r['events']): event['id'] = i
        r['counts'] = {}
        for event in r['events']: r['counts'][event['kind']] = r['counts'].get(event['kind'],0)+event['amount']
    elif kind == 'duplicate_record': r['events'].insert(1,deepcopy(r['events'][0]))
    elif kind == 'missing_record': r['events'].pop(0)
    elif kind == 'metadata': r['metadata'][plant['target']] = plant['wrong']
    elif kind == 'duplicate_output': r['value']['outputs'].append(deepcopy(r['value']['outputs'][0]))
    elif kind == 'missing_output': r['value']['outputs'].pop(0)
    else: raise ValueError(kind)
    return r

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--phase',choices=['pilot','size-pilot','controls'],required=True)
    parser.add_argument('--receipt',required=True)
    args = parser.parse_args()
    pinned = json.loads((HERE/'CONTROL-PIN.json').read_text())
    cases = pinned['controls']
    assert len(cases) == pinned['declared_controls'] > 0
    if args.phase == 'pilot': cases = cases[:3]
    if args.phase == 'size-pilot': cases = [c for c in cases if c['id'] in pinned['size_pilot_ids']]
    tick = perf_counter(); rows = []
    for case in cases:
        start = perf_counter(); report = evaluate(case)
        problems = validate(report,case)
        plants = []
        for plant in case['plants']:
            changed = corrupt(report,plant)
            catches = validate(changed,case)
            plants.append({'plant':plant,'caught':bool(catches),'diagnostics':catches,
                           'value_unchanged':changed['value']==report['value']})
        passed = not problems and all(p['caught'] for p in plants)
        rows.append({'id':case['id'],'passed':passed,'diagnostics':problems,'report':report,
                     'plants':plants,'elapsed_seconds':perf_counter()-start})
        if not passed: break
    receipt = {'created_utc':datetime.now(timezone.utc).isoformat(),'phase':args.phase,
               'declared_controls':len(cases),'completed':len(rows),'clean_passed':sum(r['passed'] for r in rows),
               'plants_declared':sum(len(c['plants']) for c in cases),
               'plants_caught':sum(p['caught'] for r in rows for p in r['plants']),
               'all_passed':len(rows)==len(cases) and all(r['passed'] for r in rows),
               'elapsed_seconds':perf_counter()-tick,'source_sha256':sha(Path(__file__)),
               'controls_sha256':sha(HERE/'CONTROL-PIN.json'),'freeze_sha256':sha(HERE/'PRE-CANDIDATE-FREEZE.json'),
               'scope':'finite structural ledger readiness only; no candidate inspected or machine-work acceptance',
               'rows':rows}
    dest = ROOT/args.receipt; assert not dest.exists()
    dest.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='rows'}))
    if not receipt['all_passed']: print(json.dumps({'FAILED':rows[-1]['id'],'diagnostics':rows[-1]['diagnostics']}))
    raise SystemExit(0 if receipt['all_passed'] else 1)

if __name__ == '__main__': main()
