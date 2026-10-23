"""Own calibrated full stored-row consumer, with explicit pinned author/own module boundary.
The only row-parser adaptation is allowed-module resolution for the current entry chain.
No raw-author audit or oracle execution. Full recursor RHS and metadata checks retained.
"""
import copy,gzip,hashlib,json,pathlib,sys
HERE=pathlib.Path(__file__).resolve().parent;OLD=HERE.parent/'postrelease-v1'
sys.path.insert(0,str(OLD))
import check_closure,check_semantics
from row_audit_metadata import expression,source_gate,rowhash
from scan_rows import read_label
RUNTIME=HERE.parents[6]/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0'
def pin(p):
 p=pathlib.Path(p);return {'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def write(n,v):
 with (HERE/n).open('x') as f:json.dump(v,f,indent=2,sort_keys=True);f.write('\n')

def own_rows(rr,allowed,expected=None):
    header=rr[0];decls=[r for r in rr[1:] if 'record' not in r]
    external=[r for r in rr[1:] if r.get('record')=='external-trust-boundary']
    if len(decls)!=header['count'] or not decls:raise ValueError('missing/zero rows')
    if any(r.get('record') not in (None,'external-trust-boundary') for r in rr[1:]):raise ValueError('unknown row')
    names=[r['name'] for r in decls]
    if len(names)!=len(set(names)):raise ValueError('duplicate declaration rows')
    externals={r['name']:r for r in external}
    if len(externals)!=len(external):raise ValueError('duplicate external rows')
    if header['import_level']!='private':raise ValueError('private imports required')
    all_refs=set();walked=0;proofs=0;recursor_rules=0
    for r in decls:
        if r['module'] not in header['modules']:raise ValueError('module provenance')
        tr,tn=expression(r['type']);walked+=tn
        if tr!=set(r['type_refs']):raise ValueError('type dependency mismatch')
        k=r['kind'];body=r['body'];payload=r['data_payload'];extra=set()
        fields={
            'definition':{'safety','hints','all'},'theorem':{'all'},'opaque':{'all'},'axiom':set(),
            'inductive':{'all','ctors','numParams','numIndices','numNested','isRec','isReflexive'},
            'constructor':{'induct','cidx','numParams','numFields'},
            'recursor':{'all','numParams','numIndices','numMotives','numMinors','k','rules'},
            'quotient':{'quotKind'}}
        if k not in fields or set(payload)!=fields[k]:raise ValueError('incomplete nonproof data payload')
        if k in ('definition','opaque'):
            if body is None or r['proof_body_omitted_after_actual_walk']:raise ValueError('nonproof body missing')
            br,bn=expression(body);walked+=bn
            if br!=set(r['body_refs']) or bn!=r['body_nodes']:raise ValueError('body walk mismatch')
        elif k=='theorem':
            if body is not None or not r['proof_body_omitted_after_actual_walk'] or r['body_nodes']<1:
                raise ValueError('proof body actual-walk attestation')
            proofs+=1
        elif body is not None or r['body_nodes']!=0 or r['body_refs']:
            raise ValueError('unexpected body')
        if k=='inductive':extra.update(payload['all']);extra.update(payload['ctors'])
        elif k=='constructor':extra.add(payload['induct'])
        elif k=='recursor':
            extra.update(payload['all'])
            for rule in payload['rules']:
                if set(rule)!={'ctor','nfields','rhs'}:raise ValueError('recursor rule payload')
                rr0,nn=expression(rule['rhs']);extra.update(rr0);extra.add(rule['ctor']);walked+=nn;recursor_rules+=1
        if extra!=set(r['extra_refs']):raise ValueError('extra dependency mismatch')
        all_refs.update(tr);all_refs.update(r['body_refs']);all_refs.update(extra)
    if all_refs-set(names)-set(externals):raise ValueError('unknown declaration reference')
    if set(externals)-all_refs:raise ValueError('extraneous trust boundary')
    for name,r in externals.items():
        if r['module'] in allowed:continue
        # Name prefixes alone are insufficient. Resolve every recorded trusted
        # module to the pinned installed runtime, with no project lookup.
        if not r['module'].startswith(('Init.','Lean.','Std.')) and r['module'] not in ('Init','Lean','Std'):
            raise ValueError('unlicensed external module')
        p=RUNTIME/'lib/lean'/pathlib.Path(*r['module'].split('.')).with_suffix('.olean')
        if not p.is_file() or not p.resolve().is_relative_to(RUNTIME.resolve()):raise ValueError('external binary path')
    if expected is not None:
        actual={r['name']:rowhash(r) for r in decls}
        if actual!=expected:raise ValueError('missing/altered row commitment')
    source_gate({r['name']:r for r in decls})
    return {r['name']:r for r in decls},{'rows':len(decls),'full_expression_nodes_walked':walked,
        'proofs_actual_walk_attested':proofs,'recursor_rules_walked':recursor_rules,'trusted_external_names':len(externals)}


from row_audit_metadata import level,metadata
DAG_PHYSICAL_NODES=0

def dag_expression(x):
 global DAG_PHYSICAL_NODES
 if not isinstance(x,list) or len(x)!=3 or x[0]!='dag-v1':raise ValueError('DAG format/refusal')
 _,root,table=x
 if type(root)is not int or not isinstance(table,list) or not table or len(table)>10000 or not 0<=root<len(table):raise ValueError('DAG root/size')
 cache=[];edges=[]
 for i,node in enumerate(table):
  if not isinstance(node,list) or not node:raise ValueError('DAG node')
  tag=node[0];refs=set();nodes=1;children=[]
  def child(v):
   nonlocal nodes
   if not isinstance(v,list) or len(v)!=2 or v[0]!='ref' or type(v[1])is not int or not 0<=v[1]<i:raise ValueError('DAG child/forward/cycle')
   j=v[1];refs.update(cache[j][0]);nodes+=cache[j][1];children.append(j)
  if tag=='const' and len(node)==3 and isinstance(node[1],str) and isinstance(node[2],list):
   for u in node[2]:level(u)
   refs.add(node[1])
  elif tag=='sort' and len(node)==2:level(node[1])
  elif tag in ('bvar','nat') and len(node)==2 and type(node[1])is int and node[1]>=0:pass
  elif tag=='str' and len(node)==2 and isinstance(node[1],str):pass
  elif tag=='app' and len(node)==3:child(node[1]);child(node[2])
  elif tag in ('lam','forall') and len(node)==5 and isinstance(node[1],str) and isinstance(node[4],str):child(node[2]);child(node[3])
  elif tag=='let' and len(node)==6 and isinstance(node[1],str) and type(node[5])is bool:child(node[2]);child(node[3]);child(node[4])
  elif tag=='proj' and len(node)==4 and isinstance(node[1],str) and type(node[2])is int and node[2]>=0:refs.add(node[1]);child(node[3])
  elif tag=='metadata' and len(node)==3:metadata(node[1]);child(node[2])
  else:raise ValueError('DAG constructor malformed/unsupported')
  cache.append((refs,nodes));edges.append(children)
 seen=set();todo=[root]
 while todo:
  i=todo.pop()
  if i in seen:continue
  seen.add(i);todo+=edges[i]
 if seen!=set(range(len(table))):raise ValueError('DAG extraneous/unreachable')
 DAG_PHYSICAL_NODES+=len(table)
 return cache[root]

expression=dag_expression

def receipt(label,expect_success=True):
 rows=[json.loads(p.read_text()) for p in (HERE/'evidence').glob('*.json') if json.loads(p.read_text()).get('label')==label]
 if len(rows)!=1:raise ValueError('receipt denominator')
 r=rows[0]
 if expect_success and (r['returncode']!=0 or r['stop_reason']):raise ValueError('supervised stage refused')
 if r['effective_caps']['raw']>16*1024**2 or r['effective_caps']['line']>8*1024**2 or r['effective_caps']['rss_bytes']>3072*1024**2:raise ValueError('resource caps')
 if expect_success and max(r['peak_sampled_root_rss_bytes'],r['peak_os_child_rss_bytes'])>r['effective_caps']['rss_bytes']:raise ValueError('peak RSS violation')
 out=[];raw=0
 for shard in r['shards']:
  p=HERE/shard['path'];assert pin(p)['sha256']==shard['sha256']
  if shard['bytes']>4*1024**2:raise ValueError('compressed shard cap')
  with gzip.open(p,'rb') as f:
   for line in f:
    raw+=len(line)
    if len(line)>4*1024**2 or raw>16*1024**2:raise ValueError('DAG chunk/raw cap')
    out.append(json.loads(line))
 assert raw==r['raw_bytes']
 return out

def calibrate():
 global DAG_PHYSICAL_NODES
 clean=receipt('dag-control-clean-v1');own_rows(clean,{'DagControl'})
 ds={r['name']:r for r in clean[1:] if 'record' not in r}
 assert {'definition','theorem','inductive','constructor','recursor','opaque'}<=set(r['kind'] for r in ds.values())
 catches=[]
 for mutation in ['missing-row','duplicate-row','missing-body','forged-reference','partial','unsafe','missing-DAG-node','forward-DAG-reference','extraneous-DAG-node','metadata-Syntax']:
  bad=copy.deepcopy(clean);r=next(r for r in bad if r.get('kind')=='definition' and r['body'])
  if mutation=='missing-row':bad.remove(r)
  elif mutation=='duplicate-row':bad.append(copy.deepcopy(r))
  elif mutation=='missing-body':r['body']=None
  elif mutation=='forged-reference':r['body_refs'].append('Forged.missing')
  elif mutation=='partial':r['partial']=True
  elif mutation=='unsafe':r['unsafe']=True
  elif mutation=='missing-DAG-node':r['body'][2].pop()
  elif mutation=='forward-DAG-reference':r['body'][2][0]=['app',['ref',0],['ref',0]]
  elif mutation=='extraneous-DAG-node':r['body'][2].append(['nat',999])
  else:
   i=len(r['body'][2]);oldroot=r['body'][1]
   r['body'][2].append(['metadata',[[['anonymous'],['syntax-unencoded','retained negative']]],['ref',oldroot]])
   r['body'][1]=i
  try:own_rows(bad,{'DagControl'})
  except (AssertionError,ValueError,TypeError,KeyError,IndexError):catches.append(mutation)
  else:raise AssertionError('DAG reader accepted '+mutation)
 try:own_rows(receipt('dag-control-hidden-v2'),{'DagControl','DagControlBadV2'})
 except (AssertionError,ValueError,TypeError):catches.append('hidden-custom-axiom')
 else:raise AssertionError('hidden axiom admitted')
 caps=receipt('dag-cap-controls-v1')
 assert caps==[['dag-refused','DAG-node-cap'],['producer-refused','DAG-chunk-cap']],caps
 for cap in caps:
  try:dag_expression(cap)
  except ValueError:pass
  else:raise AssertionError('cap marker accepted')
 catches+=['DAG-node-cap','DAG-chunk-cap']
 out={'status':'BOUNDED-DAG-CALIBRATION-CHECKED','caught':catches,'physical_nodes_validated_in_calibration':DAG_PHYSICAL_NODES,'old_full_row_schema_metadata_and_flags_retained':True,'no_expanded_expression_tree_rebuilt':True,'shared_producer_runtime_trust_declared':True,'new_blind_credit':0}
 write('DAG-CALIBRATION-CERTIFICATE-v1.json',out);print(json.dumps(out,sort_keys=True))

if __name__=='__main__':calibrate()
