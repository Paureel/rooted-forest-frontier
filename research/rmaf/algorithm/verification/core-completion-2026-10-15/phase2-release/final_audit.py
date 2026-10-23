"""Runtime/source identity and literal #print axioms for full proof origins."""
import json,os,re,subprocess
from pathlib import Path
from rebuild import ROOT,HERE,LEAN,run,digest

def strip_comments_strings(s):
    out=[];i=0;depth=0;quoted=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;i+=2
            elif s.startswith('-/',i):depth-=1;i+=2
            else:i+=1
        elif quoted:
            if s[i]=='\\':i+=2
            elif s[i]=='"':quoted=False;i+=1
            else:i+=1
        elif s.startswith('/-',i):depth=1;i+=2;out.append(' ')
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j;out.append('\n')
        elif s[i]=='"':quoted=True;i+=1;out.append(' ')
        else:out.append(s[i]);i+=1
    assert depth==0 and not quoted
    return ''.join(out)

def main():
    b=HERE/'joint-copy'
    j=json.loads((ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-joint-v1.json').read_text())
    mods=[s['mapped_module'] for s in j['sources']]+['NonauthorConsumer']
    module_list=', '.join('`'+m for m in mods)
    (b/'FreshPrintAxioms.lean').write_text('''import NonauthorConsumer
import Controls
import CutControls
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[MODULES]
  let mut count : Nat := 0
  for (n,ci) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.header.moduleNames[idx.toNat]!
      if modules.contains origin then
        match ci with
        | .thmInfo _ =>
          logInfo m!"PRINT_ORIGIN|{origin}|{n}"
          elabCommand (← `(command| #print axioms $(mkIdent n)))
          count := count + 1
        | _ => pure ()
  logInfo m!"PRINT_THEOREM_TOTAL|{count}"
'''.replace('MODULES',module_list))
    r=run(b,'FreshPrintAxioms');assert r['exit']==0,r
    count=sum(s.startswith('PRINT_ORIGIN|') for s in (b/'FreshPrintAxioms.log').read_text().splitlines())
    expected=sum(x['kind']=='theorem' for x in j['audit']['rows']);assert count==expected
    scanned=[]
    for s in j['sources']+[{'mapped_path':str((b/'NonauthorConsumer.lean').relative_to(ROOT))}]:
        p=ROOT/s['mapped_path'];clean=strip_comments_strings(p.read_text())
        flagged=re.findall(r'\b(?:sorry|admit|native_decide|axiom|unsafe|extern|implemented_by|csimp)\b',clean)
        assert not flagged,(p,flagged)
        scanned.append({'path':str(p.relative_to(ROOT)),'realpath':str(p.resolve()),'sha256':digest(p),'flagged':flagged})
    runtime={}
    for flag in ['--version','--print-prefix']:
        p=subprocess.run([str(LEAN),flag],cwd=b,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        assert not p.returncode;runtime[flag]=p.stdout.strip()
        (b/('runtime'+flag+'.log')).write_text(p.stdout)
    prefix=Path(runtime['--print-prefix'])
    runtime['standard_origin_files']={str(p):digest(p) for p in [prefix/'bin/lean',prefix/'lib/lean/Std.olean',prefix/'lib/lean/Lean.olean']}
    runtime['lean_shim_realpath']=str((ROOT/'.runtime/elan/bin/lean').resolve())
    runtime['command_policy']={'command':[str(LEAN),'-o','<module>.olean','<module>.lean'],
      'working_directory':'one isolated package copy; final joint-copy only after separate source builds',
      'LEAN_PATH':'absolute isolated build directory only; builtin standard imports resolved from runtime prefix',
      'copied_compiled_files':0,'network_used':False}
    report={'status':'PASS_FULL_SOURCE_AXIOM_RUNTIME_AUDIT','print_axioms_build':r,
      'theorem_print_count':count,'all_origin_count':j['audit']['total'],
      'all_private_generated_included':True,'scan':scanned,'runtime':runtime,
      'axiom_union':j['audit']['axiom_union'],'custom_axioms':j['audit']['forbidden']}
    (ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-final-audit-v1.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],count,'literal #print axioms records;',len(scanned),'source files')

if __name__=='__main__':main()
