"""Own oracle truth/adapter expectations frozen before first solver evaluation.

Postcontact adapter only; the original hand fixture values are unchanged.
"""
import hashlib,json,pathlib,time
from semantic_oracles import validate_input,partition_agreements,graph_agreements,trees,partitions,canon_blocks
HERE=pathlib.Path(__file__).resolve().parent
def main():
 start=time.perf_counter();out=HERE/'cases';out.mkdir();frozen=json.loads((HERE.parent/'FIXTURES-v1.json').read_text())
 batches={};expect={}
 def put(batch,row,truth):
  batches.setdefault(batch,[]).append(row);assert row['id'] not in expect;expect[row['id']]=truth
 def pair(batch,id,a,b,k):
  ps=partition_agreements(a,b);gs,_=graph_agreements(a,b);assert ps==set(gs)
  optimum=min(map(len,ps))
  put(batch,{'id':id,'mode':'external','a':a,'b':b,'k':k},{'proper':True,'optimum':optimum,
      'feasible':optimum<=k,'valid_partitions':[[list(v) for v in p] for p in sorted(ps)]})
 for f in frozen['truth_cases']:
  n=len(validate_input(f['a'],f['b']))
  for k in range(n+2):pair('hand',f'hand-{f["id"]}-k{k}',f['a'],f['b'],k)
 for f in frozen['validity_cases']:
  put('hand',{'id':'validity-'+f['id'],'mode':'agreement','a':f['a'],'b':f['b'],'blocks':f['blocks']},
      {'agreement':f['valid']})
 for f in frozen['malformed_cases']:
  typed=f['id'] in ('duplicate_leaf','different_labels')
  for k in (0,1,3):
   put('hand',{'id':f'malformed-{f["id"]}-k{k}','mode':'external','a':f['a'],'b':f['b'],'k':k},
       {'proper':False,'feasible':False} if typed else {'input_error':True,'outside_typed_Tree_API':True})
 for n in (3,4):
  tt=trees(tuple(range(n)));rows=0
  for i,a in enumerate(tt):
   for j,b in enumerate(tt):
    ps=partition_agreements(a,b);gs,_=graph_agreements(a,b);assert ps==set(gs)
    optimum=min(map(len,ps))
    bucket='n3-pilot' if n==3 else f'n4-{i//3:02d}'
    for k in range(n+2):
     put(bucket,{'id':f'n{n}-{i}-{j}-k{k}','mode':'external','a':a,'b':b,'k':k},
         {'proper':True,'optimum':optimum,'feasible':optimum<=k,
          'valid_partitions':[[list(v) for v in p] for p in sorted(ps)]})
    for q,p in enumerate(partitions(tuple(range(n)))):
     put(bucket,{'id':f'n{n}-{i}-{j}-p{q}','mode':'agreement','a':a,'b':b,
                 'blocks':[list(v) for v in p]}, {'agreement':p in ps})
    rows+=1
  assert rows=={3:9,4:225}[n]
 files=[]
 for batch,rs in batches.items():
  p=out/(batch+'.jsonl');p.write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in rs))
  files.append({'batch':batch,'path':str(p),'rows':len(rs),'bytes':p.stat().st_size,
                'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
 (HERE/'SEMANTIC-EXPECTATIONS-v1.json').write_text(json.dumps(expect,sort_keys=True)+'\n')
 manifest={'phase':'postcontact adapter; original hand expectations unchanged','batches':files,
   'total_rows':len(expect),'seconds':time.perf_counter()-start,
   'negative_output_corruptions':['false-negative','invalid-partition','wrong-optimum','root-cut','invalid-cut',
     'duplicate-cut','missing-cut','wrong-original-edge','missing-row','duplicate-row','wrong-properness']}
 (HERE/'SEMANTIC-CASE-MANIFEST-v1.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(json.dumps({'batches':len(files),'rows':len(expect),'seconds':manifest['seconds']},sort_keys=True))
if __name__=='__main__':main()
