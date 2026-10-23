#!/usr/bin/env python3
"""Check full stored-producer map, exact source/import/body digests and plants."""
import collections,copy,hashlib,importlib.util,json,pathlib,sys
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent;ROOT=pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience')
sys.path.insert(0,str(HERE.parent));import producer_runner as own

def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def write(name,obj):(HERE/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')

def main():
    data=json.loads((HERE/'AuditScientific-digest-v2.json').read_text())
    source=json.loads((HERE/'SOURCE-MAP-v1.json').read_text())
    expected={r['module']:r for r in source['copied_sources']}
    actual={p['producer']:p for p in data['producer_inventories']}
    assert set(actual)==set(expected) and len(actual)==160 and not data['rejected']
    assert len(data['stored_occurrences'])==4675 and len(data['resolved_names'])==4647
    assert json.loads((HERE/'stream-full-receipt-v2.json').read_text())['digest_fields']==18644
    data['sources']={n+'.lean':r['sha256'] for n,r in expected.items()}
    filechecks=[]
    for n,r in expected.items():
        p=pathlib.Path(actual[n]['olean_path'])
        if not p.is_absolute():p=(HERE/'build'/p).resolve()
        assert p.parent==(HERE/'build').resolve() and p.name==n+'.olean'
        assert sha(HERE/'build'/(n+'.lean'))==r['sha256']
        filechecks.append({'module':n,'source_sha256':r['sha256'],'fresh_olean_sha256':sha(p),'olean_path':str(p)})
    stored=own.occurrence_map(data['stored_occurrences'])
    resolved={r['name']:r for r in data['resolved_names']}
    assert len(resolved)==4647
    direct=[r for r in stored.values() if r['kind']=='axiom'];assert not direct
    axioms=sorted({a for r in stored.values() for a in r['resolved_dependency_axioms']})
    assert set(axioms)<={'Classical.choice','Quot.sound','propext'}
    byname=collections.defaultdict(list)
    for r in stored.values():byname[r['name']].append(r)
    duplicates={n:v for n,v in byname.items() if len(v)>1}
    assert sum(len(v)-1 for v in duplicates.values())==28
    assert all(r['resolved_kind']==resolved[r['name']]['kind'] for r in stored.values())
    assert not any(r['resolved_origin']=='UNRESOLVED' for r in stored.values())
    # Pin/public-definition correspondence: exact lines except the already
    # frozen StatePartition→GroupPartition filename adapter on the import line.
    capsule=json.loads((ROOT/'research/rmaf/algorithm/verification/both-bad-2026-10-15/PUBLIC-DEFINITIONS-v1.json').read_text())
    capsule_checks=[]
    for s in capsule['sources']:
        name=pathlib.Path(s['path']).name
        if name=='State.lean':name='GroupState.lean'
        text=(HERE/'build'/name).read_text();lines=text.splitlines(keepends=True)
        for r in s['ranges']:
            expected_text=r['text']
            if name=='GroupState.lean':expected_text=expected_text.replace('import StatePartition\n','import GroupPartition\n')
            got=''.join(lines[r['start']-1:r['end']])
            assert got==expected_text,(name,r['start'],r['end'])
            capsule_checks.append({'module':name,'start':r['start'],'end':r['end'],'exact_match':True})
    def errors(a,b):
        result=own.errors(a,b)
        if a['resolved_names']!=b['resolved_names']:result.append('resolved-map')
        if a['rejected']!=b['rejected']:result.append('rejection-map')
        return result
    assert errors(data,copy.deepcopy(data))==[]
    plants=[]
    def plant(name,fn,detector):
        d=copy.deepcopy(data);fn(d);e=errors(data,d)
        assert detector in e,(name,e)
        plants.append({'name':name,'caught':e})
    plant('missing-stored-occurrence',lambda d:d['stored_occurrences'].pop(),'occurrence-bijection')
    plant('duplicate-stored-occurrence',lambda d:d['stored_occurrences'].append(d['stored_occurrences'][0]),'duplicate-occurrence')
    plant('wrong-producer',lambda d:d['stored_occurrences'][0].update(producer='Wrong'),'occurrence-bijection')
    plant('wrong-stored-kind',lambda d:d['stored_occurrences'][0].update(kind='opaque'),'stored-record')
    plant('wrong-stored-type',lambda d:d['stored_occurrences'][0].update(type='wrong'),'stored-record')
    plant('wrong-stored-body',lambda d:d['stored_occurrences'][0].update(body='wrong'),'stored-record')
    plant('wrong-resolved-origin',lambda d:d['stored_occurrences'][0].update(resolved_origin='Wrong'),'stored-record')
    plant('wrong-resolved-map-body',lambda d:d['resolved_names'][0].update(body='wrong'),'resolved-map')
    plant('wrong-source-pin',lambda d:d['sources'].update({'RMAF.lean':'0'*64}),'sources')
    plant('wrong-import',lambda d:d['imports'].append('Hidden'),'imports')
    plant('wrong-stored-producer-import',lambda d:d['producer_inventories'][0]['imports'].append('Hidden'),'producer_inventories')
    plant('coalesced-axiom-behind-theorem',lambda d:d['stored_occurrences'][0].update(kind='axiom',resolved_kind='theorem'),'stored-direct-axiom')
    # Exact source-byte adapter detector before compilation, without mutating
    # released source: one changed byte cannot retain its pin.
    original=(HERE/'build/Dispatcher.lean').read_bytes();wanted=expected['Dispatcher']['sha256']
    assert hashlib.sha256(original).hexdigest()==wanted
    assert hashlib.sha256(original+b'\n-- deliberate adapter corruption\n').hexdigest()!=wanted
    # Independent target-overlap assertion on the ACTUAL compiled child tuple.
    loader=importlib.util.spec_from_file_location('own_graph',HERE.parent/'instrument-v2.py')
    m=importlib.util.module_from_spec(loader);loader.loader.exec_module(m)
    lines=(HERE/'compiled-controls-bank-v1.json').read_text().splitlines()
    controls=next(json.loads(x) for x in lines if x.startswith('{"cases"'))
    row=next(x for x in controls['cases'] if x['name']=='S11')
    execution=next(x for x in row['executions'] if x['q']==5 and x['oracle']==0)
    child=json.loads(execution['result'])['reported_calls'][1]
    tb=m.Original(child['target']);sourceparts=[m.Original(s).order for s in child['sources']]
    assert tb.hull(sourceparts[0])&tb.hull(sourceparts[1])
    selection=json.loads((HERE/'selection-controls-v1.json').read_text())
    assert selection['candidate_lengths']==[8,7,9,7] and selection['source_only_rejected']
    assert selection['bad_C_partitions']==[False]*3
    boundary=selection['C_clearance_boundary']
    assert all(boundary[k] for k in ['A_bad','B_bad','C_good','partition','selector_expected','source_disjoint'])
    assert boundary['C_clear_A']==boundary['C_clear_B']==False
    for r in selection['selection']:
        result=json.loads(r['result']);assert result['reported']==r['observed']==[0,1,2,1]
        if r['kind']==0:assert len(result['answer'])==7
        else:assert result['answer'] is None
    summary={'status':'PASS_STORED_PRODUCER_KERNEL_SCOPE','scientific_producers':160,
      'stored_occurrences':4675,'resolved_names':4647,'coalesced_occurrence_excess':28,
      'direct_scientific_axioms':0,'dependency_axioms':axioms,
      'private_stored_occurrences':sum(r['name'].startswith('_private.') for r in stored.values()),
      'generated_recursors':sum(r['kind']=='recursor' for r in stored.values()),
      'compiler_auxiliary_names_inventoried':sum(len(p['compiler_extra_names']) for p in actual.values()),
      'corruption_plants_caught':len(plants),'source_byte_adapter_plant_caught':True,
      'public_excerpt_checks':len(capsule_checks),'selection_controls':3,
      'actual_internal_B_target_overlap_confirmed':True,
      'limits':['Compiler auxiliary names are inventoried, not kernel ConstantInfo bodies.',
                'No compiled instruction identity or runtime correspondence follows.'],
      'filechecks':filechecks,'capsule_checks':capsule_checks,'plants':plants,
      'coalesced_occurrences':duplicates}
    write('PROVENANCE-CHECKS-v1.json',summary)
    print(json.dumps({k:v for k,v in summary.items() if k not in ['filechecks','capsule_checks','plants','coalesced_occurrences']},indent=2))

if __name__=='__main__':main()
