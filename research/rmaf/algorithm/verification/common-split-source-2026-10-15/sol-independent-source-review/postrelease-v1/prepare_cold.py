#!/usr/bin/env python3
"""One-shot own released-source registry/header scan. No author auditor imports."""
import hashlib,json,pathlib,re
P=pathlib.Path(__file__).resolve().parent
registry=json.loads((P/'COLD-SOURCE-REGISTRY-v1.json').read_text());by={r['module']:r for r in registry}

def lexical_code(s):
    # Retain offsets/newlines while excluding nested comments and literal strings.
    out=list(s);i=0;n=len(s);depth=0
    while i<n:
        if depth:
            if s.startswith('/-',i):out[i:i+2]='  ';depth+=1;i+=2
            elif s.startswith('-/',i):out[i:i+2]='  ';depth-=1;i+=2
            else:
                if s[i]!='\n':out[i]=' '
                i+=1
        elif s.startswith('/-',i):out[i:i+2]='  ';depth=1;i+=2
        elif s.startswith('--',i):
            while i<n and s[i]!='\n':out[i]=' ';i+=1
        elif s[i]=='"':
            out[i]=' ';i+=1
            while i<n:
                if s[i]=='\\':out[i]=' ';i+=1
                elif s[i]=='"':out[i]=' ';i+=1;break
                if i<n:
                    if s[i]!='\n':out[i]=' '
                    i+=1
        else:i+=1
    if depth:raise ValueError('unclosed comment')
    return ''.join(out)

imports={};flags=[];commands=[]
for r in registry:
    raw=pathlib.Path(r['source']).read_text();code=lexical_code(raw);im=[]
    for ln,line in enumerate(code.splitlines(),1):
        stripped=line.strip()
        match=re.fullmatch(r'(?:(public|meta)\s+)*import\s+(.*)',stripped)
        if match:
            tokens=match.group(2).split();allflag=False
            if tokens and tokens[0]=='all':allflag=True;tokens=tokens[1:]
            if not tokens or any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',t) for t in tokens):raise ValueError(('unsupported import header',r['module'],ln,stripped))
            for t in tokens:im.append({'module':t,'line':ln,'all':allflag,'source_header':line})
        elif re.search(r'\bimport\b',stripped):raise ValueError(('unparsed import token',r['module'],ln,stripped))
        if re.search(r'\b(axiom|unsafe|partial|sorry|admit|native_decide|run_elab|elab|macro)\b|skipKernelTC|trustCompiler',line):flags.append({'module':r['module'],'line':ln,'code':line.strip()})
        if re.search(r'^\s*(set_option|#eval|#check|#print)',line):commands.append({'module':r['module'],'line':ln,'code':line.strip()})
    for i in im:
        if i['module'] not in by and i['module'].split('.')[0] not in ('Std','Init','Lean'):raise ValueError(('unmapped import',r['module'],i))
    imports[r['module']]=im
order=[];active=set();done=set()
def visit(m):
    if m in done:return
    if m in active:raise ValueError(('import cycle',m))
    active.add(m)
    for i in imports[m]:
        if i['module'] in by:visit(i['module'])
    active.remove(m);done.add(m);order.append(m)
for m in by:visit(m)
root='DerivedMinimum';closure=set()
def reach(m):
    if m in closure:return
    closure.add(m)
    for i in imports[m]:
        if i['module'] in by:reach(i['module'])
reach(root)
out={'modules':len(by),'imports':imports,'topological_order':order,'derived_minimum_transitive_modules':sorted(closure),'flagged_noncomment_tokens':flags,'source_commands':commands,'header_parser_scope':'line-oriented simple import headers; unsupported tokens fail; exact compiler Import arrays/modifiers compared later','copied_binary_count_before_build':len(list((P/'cold').glob('*.olean')))}
assert out['copied_binary_count_before_build']==0
(P/'SOURCE-HEADER-AUDIT-v1.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({'modules':len(by),'derived_closure':len(closure),'flagged_tokens':flags,'commands':commands,'first_modules':order[:8],'copied_binaries':out['copied_binary_count_before_build']},sort_keys=True))
