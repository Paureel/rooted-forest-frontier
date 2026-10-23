"""Fresh source-only dependency planner from exact canonical manifest members."""
import hashlib,json,pathlib,re,time
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parent.parents[5]
MP=ROOT/'research/rmaf/algorithm/universal233/ordinary_dispatch/fast_ordinary_recursion/FINAL-MANIFEST-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 start=time.perf_counter();m=json.loads(MP.read_text());canonical=m['canonical_build'].rstrip('/')+'/'
 members={r['path']:r for r in m['immutable_files']}
 sources={p[len(canonical):-5].replace('/','.'):(ROOT/p) for p in members
          if p.startswith(canonical) and p.endswith('.lean') and '/' not in p[len(canonical):]}
 done=set();visiting=set();order=[];info={};alerts=[]
 def visit(name):
  if name in done:return
  if name in visiting:raise ValueError(('cycle',name))
  if name not in sources:
   if name=='Init' or name.startswith(('Init.','Lean','Std')):return
   raise ValueError(('unlicensed source import',name))
  visiting.add(name);p=sources[name];r=members[str(p.relative_to(ROOT))]
  assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256']
  text=p.read_text();imports=[]
  # Existing sources use one-line imports. Block comments are removed before
  # header scanning; any unrecognized import syntax is a recorded stop.
  clean=re.sub(r'/\-.*?\-/','',text,flags=re.S)
  for line in clean.splitlines():
   line=line.split('--',1)[0].strip()
   match=re.match(r'(?:(?:public|private|meta)\s+)?import\s+(.+)$',line)
   if match:
    tokens=match.group(1).split()
    if not all(re.fullmatch(r'[A-Za-z0-9_.]+',x) for x in tokens):raise ValueError(('header syntax',name,line))
    imports.extend(tokens)
  commands=[(i+1,line[:250]) for i,line in enumerate(clean.splitlines())
            if re.match(r'\s*(#eval|#guard|run_cmd|run_meta|initialize|builtin_initialize)\b',line)]
  if commands:alerts.append({'module':name,'commands':commands})
  for dep in imports:visit(dep)
  info[name]={'source':str(p),'sha256':r['sha256'],'bytes':r['bytes'],'imports':imports}
  visiting.remove(name);done.add(name);order.append(name)
 visit('FastExact')
 plan={'version':1,'canonical_build':canonical,'entrypoint':'FastExact','source_count':len(order),
       'order':order,'modules':info,'command_alerts':alerts,'seconds':time.perf_counter()-start,
       'source_copy_performed':False,'binary_copy_performed':False}
 (HERE/'COLD-SOURCE-PLAN-v1.json').write_text(json.dumps(plan,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'source_count':len(order),'alerts':alerts,'first_modules':order[:12],
                   'last_modules':order[-12:],'seconds':plan['seconds']},sort_keys=True))
if __name__=='__main__':main()
