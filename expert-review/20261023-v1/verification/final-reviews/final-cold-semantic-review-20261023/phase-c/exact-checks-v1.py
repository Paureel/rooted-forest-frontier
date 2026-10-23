import json,sys,runpy
from pathlib import Path


def encode(t,s):
 def post(t):
  if isinstance(t,int):
   bits=[int(c) for c in bin(t)[2:]]
   return [0,0]+[1]*len(bits)+[0]+bits
  return post(t[0])+post(t[1])+[1,0]
 bits=post(t)+[0,1]+post(s)+[0,1]
 return (1<<len(bits))+sum(b<<i for i,b in enumerate(bits)),len(bits)


def decode(raw,wrong=False):
 u=raw;stack=[];roots=[];words=1;digits=0
 def digit():
  nonlocal u,digits
  if u<=1:raise ValueError('TRUNCATED')
  z=u&1;u>>=1;digits+=1;return z
 while True:
  tag=digit()+2*digit()
  if tag==0:
   width=0
   while digit()==1:width+=1
   if width==0:raise ValueError('BAD_NAT')
   x=digit()
   if width>1 and x==0:raise ValueError('BAD_NAT')
   for _ in range(width-1):x=2*x+digit()
   stack.append(x);words+=5
  elif tag==1:
   if len(stack)<2:raise ValueError('STACK')
   r=stack.pop();l=stack.pop();stack.append((r,l) if wrong else (l,r));words+=6
  elif tag==2:
   if len(stack)!=1 or len(roots)>=2:raise ValueError('BOUNDARY')
   roots.append(stack.pop())
   if len(roots)==2:
    if u!=1:raise ValueError('TRAILING')
    return tuple(roots),words,digits
  else:raise ValueError('BAD_TAG')


def run_word(jobs,b,parent,child):
 calls=[];slots=[];answers=[];events=[]
 for i,p in enumerate(jobs):
  enabled=b<parent
  a=None
  if enabled:
   events.append(i);a=child(p,b)
  ret=None if a is None else (max(len(a)-1,0),a)
  calls.append(b);slots.append(dict(index=len(slots),query=(p,b),returned=ret,live=enabled))
  if ret is None:return dict(answers=None,calls=calls,visits=len(calls),slots=slots,events=events)
  answers.append(ret)
 return dict(answers=answers,calls=calls,visits=len(calls),slots=slots,events=events)


def require(x,diagnostic):
 if not x:raise ValueError(diagnostic)


def expect_bad(f,diag):
 try:f()
 except ValueError as e:
  require(str(e)==diag,'WRONG_DIAGNOSTIC');return diag
 raise ValueError('MISSED_CORRUPTION')


def gamma(f,c):return 9*f*f+63*f+3*c+62


def calibration():
 positives=[];negative=[]
 require(decode(25156)==((0,0),11,14),'LEAF_DECODE');positives.append('hand raw25156 -> two Leaf0,11words,14digits')
 try:decode(7)
 except ValueError as e:require(str(e)=='BAD_TAG','BAD_TAG_CONTROL')
 else:raise ValueError('BAD_TAG_MISSED')
 positives.append('raw7 -> BAD_TAG')
 word,_=encode((0,1),(1,0))
 negative.append(expect_bad(lambda:require(decode(word,True)[0]==((0,1),(1,0)),'DECODE_ORDER_MISMATCH'),'DECODE_ORDER_MISMATCH'))
 oracle=lambda p,b:None if p=='bad' else [[0]]
 r=run_word(['good','good','bad','unvisited'],0,1,oracle)
 require(r['visits']==3 and r['events']==[0,1,2] and [s['live'] for s in r['slots']]==[True,True,True] and r['answers'] is None,'RUN_POSITIVE')
 positives.append('duplicate successes followed by live failure stop fourth')
 collapsed={str(s['query']):i for i,s in enumerate(r['slots'])}
 negative.append(expect_bad(lambda:require(len(collapsed)==len(r['slots']),'OCCURRENCE_COLLAPSE'),'OCCURRENCE_COLLAPSE'))
 negative.append(expect_bad(lambda:require(False==r['slots'][2]['live'],'LIVE_REFUSAL_CONFUSION'),'LIVE_REFUSAL_CONFUSION'))
 recorded=[(0,0),(0,1),(2,0)];chrono=[(2,0),(0,0),(0,1)]
 require([x for block in reversed([[(0,0),(0,1)],[],[(2,0)]]) for x in block]==chrono,'TAIL_FIRST_POSITIVE');positives.append('tail first preserves inner order')
 negative.append(expect_bad(lambda:require(recorded==chrono,'CHRONOLOGY_MISMATCH'),'CHRONOLOGY_MISMATCH'))
 negative.append(expect_bad(lambda:require(None==[[0]],'NONFUNCTIONAL_R'),'NONFUNCTIONAL_R'))
 require(gamma(3,2)==338 and 9*3==27,'GAMMA_POSITIVE');positives.append('f3 c2 gamma338 F27')
 negative.append(expect_bad(lambda:require(gamma(3,2)==337,'GAMMA_FORMULA_MISMATCH'),'GAMMA_FORMULA_MISMATCH'))
 require(16*max(2**30,2**22,2**18,2**16)==2**34,'MATERIAL_POSITIVE');positives.append('m0 correct material max equality')
 negative.append(expect_bad(lambda:require(16*2**30<=16*max(2**22,2**18,2**16),'UNDERABSORBED_MATERIALIZATION'),'UNDERABSORBED_MATERIALIZATION'))
 return dict(positive_count=len(positives),positive_observations=positives,negative_count=len(negative),exact_negative_diagnostics=negative)


def candidate():
 own=runpy.run_path('research/rmaf/algorithm/verification/final-cold-semantic-review-20261023/phase-b/closed-checks-v1.py')
 body_traces=[]
 def child(pair,b):
  tr=[];a=own['query'](b,*pair,tr);body_traces.append(dict(pair=pair,budget=b,value=a,trace=tr));return a
 jobs=[(0,0),(0,0),(0,1),(0,0)]
 r=run_word(jobs,0,1,child)
 require(r['visits']==3 and r['events']==[0,1,2] and len(body_traces)==3 and r['answers'] is None,'GROUNDED_RUN')
 require(r['slots'][0]['query']==r['slots'][1]['query'] and r['slots'][0]['index']!=r['slots'][1]['index'],'DUPLICATE_INDEX')
 require(r['slots'][2]['live'] and r['slots'][2]['returned'] is None,'LIVE_FAILURE')
 refused=run_word(jobs,1,1,child)
 require(refused['events']==[] and len(body_traces)==3 and refused['slots'][0]['live']==False and refused['slots'][0]['returned'] is None,'CUTOFF_REFUSAL')
 h=2**80+3;t=((h,3),(5,(7,9)));s=(((h,5),3),(9,7));raw,bits=encode(t,s)
 decoded,words,digits=decode(raw)
 require(decoded==(t,s) and words==99 and digits==bits and raw.bit_length()==bits+1,'FIVE_LEAF_DECODER')
 f=735030;c=367508;F=9*f;g=gamma(f,c);sc=3*f+c+128
 require((F,g,sc)==(6615270,4862469317576,2572726),'FIXED_CONSTANTS')
 coeffs=[4096,512,512,512,24,272,2048,72,512,5120,16384,2048,3072,1536,1024,20480,32768,2048,1024,2048,4096,8192]
 require(sum(coeffs)==108400 and sum(coeffs)<2**17,'PAYLOAD_SUM')
 slacks=[]
 for a in range(2,65):
  slack=2048*a*a-(296*a*a+3416*a+160);require(slack>=0,'ENVIRONMENT_BOUND');slacks.append(slack)
 for m in range(65):
  x=(m+1)**3;require(16*max(2**30,2**22*x,2**18,2**16)<=2**34*x,'MATERIAL_BOUND')
 count=0;max_scalar_bits=0
 for n in range(1,9):
  for q in range(n):
   for l in [1,3,81]:
    R=n+q+l+2;Pprime=2**48*(2**18*(n+1)**3+1)**10;K=2**252*R**32
    require(256*Pprime<=K and Pprime<=2**238*R**30,'K_ABSORPTION')
    d0=10*n+4*n*l+1;ui=512*(d0+1);h0=1+F*ui;vi=d0+q+h0+f+c+8;I=16*g*ui*(vi+1)**2;D=d0+l+2*(q+n)+sc+16
    for p in [0,1,17,10**30+7]:
     C=p*4**q;u=K*(C+1);J=h0+F*K*(p+1);Z=16*sc*R**4*(K+1)**4;T=Z*(p+1)**4;B=D+T+J+10*q+4
     actual_h=h0+F*u;actual_x=2**D+16*sc*R**4*(u+1)**4
     require(actual_h<=J*4**q and actual_h.bit_length()<=J+2*q+1<=B,'POINTER_WIDTH')
     require(actual_x.bit_length()<=D+8*q+T+2<=B,'SCALAR_WIDTH')
     A=I+16*g*K*(B+1)**2;bill=I+16*g*(B+1)**2*u
     require(bill<=A*(C+1),'FINAL_BILL_BOUND')
     max_scalar_bits=max(max_scalar_bits,actual_x.bit_length());count+=1
 return dict(grounded_run=r,actual_child_body_traces=body_traces,cutoff_refusal=refused,decoder=dict(trees=decoded,raw=raw,digits=digits,width=raw.bit_length(),raw_heap_words=words),fixed_constants=dict(f=f,c=c,F=F,gamma=g,s=sc),payload_sum=sum(coeffs),environment_minimum_slack=min(slacks),environment_cases=len(slacks),materialization_cases=65,exact_bridge_parameter_instances=count,maximum_tested_scalar_bitlength=max_scalar_bits,scope='closed Run/decoder instances and exact bridge algebra; no kernel, actual full-source meter or instruction-listing execution')


if __name__=='__main__':
 mode=sys.argv[1];result=calibration() if mode=='calibration' else candidate() if mode=='candidate' else None
 if result is None:raise ValueError('UNKNOWN_MODE')
 output=Path(sys.argv[2]);output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(mode=mode,output=str(output),observations=result),indent=2))
