#!/usr/bin/env python3
"""One-shot lossless-DAG producer/origin analysis, before name coalescence.
Raw records are retained. Dependencies are read from AST nodes (including
projection structure names), not trusted from a proof-type-only summary.
"""
import collections
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import time

HERE=Path(__file__).resolve().parent
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
BUILD=HERE/'postrelease-v1-scientific'

def require(c,m):
    if not c:raise AssertionError(m)

def name_string(name):
    if name[0]=='anonymous':return ''
    p=name_string(name[1]);value=str(name[2]);return p+'.'+value if p else value

def name_lean(name):
    if name[0]=='anonymous':return 'Name.anonymous'
    if name[0]=='str':return '(Name.str '+name_lean(name[1])+' '+json.dumps(name[2])+')'
    return '(Name.num '+name_lean(name[1])+' '+str(name[2])+')'

def expression_refs(expr,structural):
    if expr is None:return set(),set()
    references=set();projections=set()
    nodes=expr['nodes'];root=expr['root']
    require(0<=root<len(nodes),'DAG root range')
    for i,node in enumerate(nodes):
        tag=node[0]
        if tag in ('const','proj'):
            name=name_string(node[1]);references.add(name);structural[name]=node[1]
            if tag=='proj':projections.add(name)
        children={'app':node[1:3],'lam':node[2:4],'forall':node[2:4],
                  'let':node[2:5],'mdata':node[2:3],'proj':node[3:4]}.get(tag,[])
        require(all(type(j)is int and 0<=j<i for j in children),'DAG child topological range')
    stored=set(expr['refs'])
    require(stored<=references and references-stored<=projections,'auxiliary refs mismatch beyond projections')
    return references,references-stored

def normalize(record):
    record=json.loads(json.dumps(record))
    for expr in [record['type'],record['body']]+[r['rhs'] for r in record['rules']]:
        if expr is not None:expr.setdefault('source_strings',[])
    return record

start=time.perf_counter();require(shutil.disk_usage(HERE).free>=3*2**30,'disk floor')
receipts=['postrelease-v1-dag-pilot.json','postrelease-v1-dag-full.json',
          'postrelease-v1-dag-metadata-pilot.json','postrelease-v1-dag-resume.json']
raw=[];merged=[];scans=[];structural={}
for receipt in receipts:
    d=json.loads((HERE/receipt).read_text())
    # A failed receipt's scans list contains only fully successful groups.
    for scan in d['scans']:
        p=ROOT/scan['gzip_path'];require(hashlib.sha256(p.read_bytes()).hexdigest()==scan['gzip_sha256'],'gzip pin')
        scans.append({'receipt':receipt,'modules':scan['modules'],'gzip_path':scan['gzip_path']})
        with gzip.open(p,'rt') as stream:
            for line in stream:
                if not line.startswith('PRODUCER '):continue
                r=json.loads(line[9:])
                if r['layer']=='raw-module':raw.append(r)
                elif r['layer']=='coalesced':merged.append(r)

build=json.loads((HERE/'postrelease-v1-build-full.json').read_text())
modules={r['module'] for r in build['closure']}
require(collections.Counter(m for s in scans for m in s['modules'])==collections.Counter(modules),'exact module scan coverage')
by_module=collections.defaultdict(list);by_name=collections.defaultdict(list)
refs_by_name={};projection_augmentations=[];body_only=[]
for r in raw:
    c=r['producer'];name=c['name'];by_module[r['module']].append(r);by_name[name].append(r)
    type_refs,extra=expression_refs(c['type'],structural)
    body_refs,extra_body=expression_refs(c['body'],structural)
    for rule in c['rules']:
        rs,extra_rule=expression_refs(rule['rhs'],structural);body_refs|=rs;extra_body|=extra_rule
        ctor=name_string(rule['ctor']);body_refs.add(ctor);structural[ctor]=rule['ctor']
    if extra or extra_body:projection_augmentations.append({'producer':name,'names':sorted(extra|extra_body)})
    # Preserve the union of every stored occurrence before name grouping;
    # proof variants can refer to different module-private splitters.
    refs_by_name.setdefault(name,set()).update(type_refs|body_refs)
    if body_refs-type_refs:body_only.append({'name':name,'body_only_refs':sorted(body_refs-type_refs)})

for module,rows in by_module.items():
    require(sorted(r['producer_index'] for r in rows)==list(range(len(rows))),'producer index completeness: '+module)
    require(all(r['declared_name_count']==len(rows) for r in rows),'stored name/producer denominator: '+module)
require(set(by_module)==modules,'all module origins represented')

collisions=[]
for name,rows in by_name.items():
    if len(rows)>1:
        versions=[normalize(r['producer']) for r in rows]
        collisions.append({'name':name,'origins':[r['module'] for r in rows],
                           'identical_stored_records':all(v==versions[0] for v in versions),
                           'identical_types':all(v['type']==versions[0]['type'] for v in versions),
                           'all_proof_theorems':all(v['kind']=='theorem' for v in versions)})
require(not any(not c['identical_stored_records'] and not(c['identical_types'] and c['all_proof_theorems'])
                for c in collisions),'different nonproof value or theorem type collision')
merge_mismatch=[]
for r in merged:
    name=r['producer']['name'];matches=by_name.get(name,[])
    if not any(normalize(m['producer'])==normalize(r['producer']) and m['module']==r['origin'] for m in matches):
        merge_mismatch.append({'name':name,'origin':r['origin']})
require(not merge_mismatch,'coalesced kind/type/body/origin mismatch')

axioms=[{'module':r['module'],'name':r['producer']['name']} for r in raw if r['producer']['kind']=='axiom']
unsafe=[{'module':r['module'],'name':r['producer']['name'],'extra':r['producer']['extra']}
        for r in raw if r['producer']['extra'] is not None
        and ('unsafe' in str(r['producer']['extra']).lower() or 'partial' in str(r['producer']['extra']).lower())]
# Store exact flags; the word 'unsafe' can occur in a false-valued metadata key.
truly_unsafe=[r for r in unsafe if r['extra'].get('unsafe') is True or
               r['extra'].get('safety') in ('Lean.DefinitionSafety.unsafe','Lean.DefinitionSafety.partial')]
private=[r['producer']['name'] for r in raw if r['producer']['name'].startswith('_private.')]
all_refs=set().union(*refs_by_name.values())
project_refs=all_refs&set(by_name)
external_refs=all_refs-set(by_name)

out=HERE/'postrelease-v1-origin-analysis-v2.json';require(not out.exists(),'preserve analysis evidence')
result={'status':'PASS','raw_occurrences':len(raw),'distinct_names':len(by_name),'modules':len(modules),
        'coalesced_records_checked':len(merged),'kind_counts':dict(collections.Counter(r['producer']['kind'] for r in raw)),
        'axioms':axioms,'truly_unsafe_or_partial':truly_unsafe,'private_producers':len(private),
        'collisions':collisions,'merge_mismatches':merge_mismatch,
        'project_references':len(project_refs),'external_reference_count':len(external_refs),
        'external_references':sorted(external_refs),'body_only_dependency_producers':len(body_only),
        'projection_reference_augmentations':projection_augmentations,'scans':scans,
        'module_producer_counts':{m:len(r) for m,r in sorted(by_module.items())},
        'seconds':time.perf_counter()-start,'disk_free_after':shutil.disk_usage(HERE).free}
out.write_text(json.dumps(result,indent=2)+'\n')

# Resolve each actual syntactic reference against the fresh complete import environment.
names=sorted(all_refs)
probe=BUILD/'IndependentReferenceOrigins.lean'
probe.write_text('import ForestPretestWork\nimport PostreleaseProducerAuditV2\nopen Lean Elab Command IndependentProducer\n'
                 'run_cmd do\n  let env ← getEnv\n  let names : List Name := ['+
                 ','.join(name_lean(structural[n]) for n in names)+']\n'+
                 '  for n in names do\n    let some c := env.find? n | throwError "unresolved reference {n}"\n'+
                 '    let origin := match env.getModuleIdxFor? n with\n'+
                 '      | none => "current-or-unresolved"\n'+
                 '      | some i => env.header.modules[i]!.module.toString\n'+
                 '    liftIO <| IO.println ("REFERENCE " ++ (Json.mkObj [("name",toJson n.toString),("origin",toJson origin),("kind",toJson (kind c))]).compress)\n'+
                 '#print axioms ForestPretest01.universal_coverage\n'+
                 '#print axioms ForestPretest01.found_globally_minimum\n'+
                 '#print axioms ForestPretest01.rejected_lower_bound\n'+
                 '#print axioms ForestPretest01.refused_iff\n'+
                 '#print axioms ForestPretest01.candidates_count\n')
print(json.dumps({k:result[k] for k in ('status','raw_occurrences','distinct_names','modules','kind_counts','axioms','private_producers','external_reference_count','seconds','disk_free_after')}
                 | {'reference_probe_names':len(names)}))
