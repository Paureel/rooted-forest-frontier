#!/usr/bin/env python3
"""One-shot same-lineage supplemental runtime observations; postcontact only."""
import collections,copy,json,os,subprocess,time
import continuation_v1 as c
import literal_adaptor_v3 as a
P=c.P;POST=c.POST;spec=json.loads((P/'SUPPLEMENTAL-EXPECTATIONS-v1.json').read_text());e=spec['ordinary_failure_case']
def tree(t):return '(.leaf '+str(t)+')'if type(t)is int else'(.node '+tree(t[0])+' '+tree(t[1])+')'
def ls(x):return json.dumps(x,separators=(',',':')).replace('false','false').replace('true','true')
def generate():
    d=a.g.setup(e);ts=d['trees'];s=(POST/'Readouts_v3.lean').read_text().split('def d0 : Setup')[0]
    s+='def ds : Setup := {\n'
    for k,v in dict(T=e['T'],S=e['S'],tx=ts['TX'],sx=ts['SX'],ty=ts['TY'],sy=ts['SY'],mxT=ts['TMX'],mxS=ts['SMX'],myT=ts['TMY'],myS=ts['SMY']).items():s+=' '+k+' := '+tree(v)+'\n'
    for k,v in [('X',e['X']),('Y',e['Y'])]:s+=' '+k+' := '+ls(v)+'\n'
    for k,v in [('x',e['repX']),('y',e['repY']),('rho',10),('gamma',11)]:s+=' '+k+' := '+str(v)+'\n'
    for key in ['T','S']:s+=' edge'+key+' := ⟨[true],'+tree(e[key][1])+',by decide,by decide,Or.inl (by decide)⟩\n'
    for k in ['nt','ns','hpT','hpS','htx','hsx','hty','hsy','hMXT','hMXS','hMYT','hMYS','hx','hy','frT','frS','fgT','fgS']:s+=' '+k+' := by decide\n'
    s+='}\ndef main : IO Unit := do\n'
    for q in range(4):s+=' row '+json.dumps(e['id'])+' ds '+str(q)+' '+ls(e['callback_FX'])+' '+ls(e['callback_FM'])+'\n'
    s+=' witness '+json.dumps(e['id'])+' ds '+ls(e['global_witness'])+'\n'
    s+=' IO.println <| (Json.mkObj [("kind",toJson "DUPLICATE_RAW"),("candidates",toJson (mergeCandidates [0] [1,2,3] 0 1 10 11 [[0,10],[0,10]] [[1],[11,3,2]]))]).compress\n'
    s+='end IndependentCallerReadout\ndef main := IndependentCallerReadout.main\n';f=P/'SupplementalReadouts_v1.lean';assert not f.exists();f.write_text(s)
    c.write('SUPPLEMENTAL-PINS-v1.json',{'source_sha256':c.sha(f),'script_sha256':c.sha(__file__),'spec_sha256':c.sha(P/'SUPPLEMENTAL-EXPECTATIONS-v1.json'),'head_reused_from':str(POST/'Readouts_v3.lean'),'head_source_sha256':c.sha(POST/'Readouts_v3.lean'),'same_lineage':True,'replication_credit':0})
    # Hand constructed controls go through same original graph oracle before new Lean evaluation.
    assert a.g.g.agreement(d['T'],d['S'],e['global_witness'])and len(e['global_witness'])-1==2
    for label,Ta,Sb,F in [('X','TX','SX',e['callback_FX']),('MX','TMX','SMX',e['callback_FM'])]:assert a.g.g.agreement(ts[Ta],ts[Sb],F)and len(F)-1==1
    assert not a.g.g.agreement(d['T'],d['S'],[[0,1,2,3,4,5]])
    c.write('SUPPLEMENTAL-PLANTED-CONTROLS-v1.json',{'status':'PASS','clean_original_cost2_witness':True,'clean_callbacks_minimum1_witnesses':True,'corrupt_one_block_rejected':True,'postcontact':True,'credit':0})
def run():
    assert json.loads((P/'SUPPLEMENTAL-PLANTED-CONTROLS-v1.json').read_text())['status']=='PASS'
    f=P/'SupplementalReadouts_v1.lean';pins=json.loads((P/'SUPPLEMENTAL-PINS-v1.json').read_text());assert c.sha(f)==pins['source_sha256'];at=time.perf_counter();env=dict(os.environ,LEAN_PATH=str(POST/'scientific-build'));cmd=[str(c.LEAN),'--run',f.name];r=subprocess.run(cmd,cwd=P,env=env,text=True,capture_output=True,timeout=120)
    (P/'supplemental-v1.stdout.log').write_text(r.stdout);(P/'supplemental-v1.stderr.log').write_text(r.stderr)
    rows=[json.loads(l)for l in r.stdout.splitlines()if l.startswith('{')];traces=[l.split('|')[1:]for l in r.stderr.splitlines()if l.startswith('TRACE|')]
    c.write('SUPPLEMENTAL-RAW-v1.json',{'returncode':r.returncode,'command':cmd,'LEAN_PATH':env['LEAN_PATH'],'source_sha256':c.sha(f),'rows':rows,'trace':traces,'seconds':time.perf_counter()-at})
    assert r.returncode==0 and len(rows)==6
    d=a.g.setup(e);ts=d['trees'];actual=rows[:4];assert [x['q']for x in actual]==list(range(4))
    truth=a.g.check_case(e)
    for row in actual:
        q=row['q'];assert row['status']==e['answers'][str(q)];assert row['callback_replies']==([]if q==0 else[None,None]if q==1 else[e['callback_FX'],e['callback_FM']])
        a.pretest(e,row,'outside',d);a.pretest(e,row,'marked_outside',d)
        cs=a.candidates(e,row['FM'],row['FN']);assert row['candidate_multiset']==cs
        valid=[F for F in cs if a.g.g.agreement(d['T'],d['S'],F)];assert row['valid_candidates']==valid and row['pick']==a.best(d['T'],d['S'],cs)
        if q>=2:assert row['result']==row['pick']and a.g.g.agreement(d['T'],d['S'],row['result'])and len(row['result'])-1==2
        else:assert row['result']is None
        observed=[(x[2],int(x[3]))for x in traces if int(x[1])==q];assert collections.Counter(observed)==collections.Counter([]if q==0 else[('ordinaryX',q-1),('markedX',q-1)])
    raw=rows[-1]['candidates'];de=dict(e,X=[0],Y=[1,2,3],repX=0,repY=1)
    assert raw==a.candidates(de,[[0,10],[0,10]],[[1],[11,3,2]])and len(raw)==4 and len(set(map(a.literal,raw)))==2
    c.write('SUPPLEMENTAL-COMPARISON-v1.json',{'status':'PASS','postcontact':True,'blind_credit':0,'replication_credit':0,'semantic_rows':4,'witness_rows':1,'raw_duplicate_control_rows':1,'actual_calls':len(traces),'q1_both_callbacks_none':True,'q2_q3_minimum_cost':2,'raw_candidates':4,'distinct_raw_values':2,'hand_cost_and_witness_only_no_global_family_claim':True,'same_oracle_check':truth,'seconds':time.perf_counter()-at})
    print(json.dumps({'supplement':'PASS','rows':6,'calls':len(traces),'q1_both_callbacks_none':True,'raw_duplicates_preserved':2}))
if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['generate','run']);args=ap.parse_args();{'generate':generate,'run':run}[args.mode]()
