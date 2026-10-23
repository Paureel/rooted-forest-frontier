#!/usr/bin/env python3
"""Postcontact lossless metadata extension; frozen detector remains unchanged."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

HERE=Path(__file__).resolve().parent
BUILD=HERE/'postrelease-v1-scientific'
LEAN=Path('/Users/paurel/Documents/ChatGPT/bootscience/.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean')
source=(BUILD/'PostreleaseProducerAudit.lean').read_text()
begin=source.index('def dataJson :')
end=source.index('\nstructure Dag where',begin)
source=source[:begin]+source[end+1:]
source=source.replace('  refs : Std.HashSet Name := {}','  refs : Std.HashSet Name := {}\n  strings : Array String := #[]\n  stringIds : Std.HashMap String Nat := {}')
anchor='abbrev Build := StateT Dag (Except String)\n'
extension=r'''
def internString (text : String) : Build Nat := do
  if let some i := (← get).stringIds[text]? then return i
  let i := (← get).strings.size
  modify fun s => { s with strings := s.strings.push text, stringIds := s.stringIds.insert text i }
  return i

def rawSubstringJson (raw : Substring.Raw) : Build Json := do
  let i ← internString raw.str
  return arr [str "raw-substring",num i,num raw.startPos.byteIdx,num raw.stopPos.byteIdx]

def sourceInfoJson : SourceInfo → Build Json
  | .none => pure (arr [str "none"])
  | .synthetic p q canonical => pure (arr [str "synthetic",num p.byteIdx,num q.byteIdx,toJson canonical])
  | .original leading p trailing q => do
      let a ← rawSubstringJson leading
      let b ← rawSubstringJson trailing
      return arr [str "original",a,num p.byteIdx,b,num q.byteIdx]

def preresolvedJson : Syntax.Preresolved → Json
  | .namespace n => arr [str "namespace",nameJson n]
  | .decl n fields => arr [str "decl",nameJson n,toJson fields]

partial def syntaxJson : Syntax → Build Json
  | .missing => pure (arr [str "missing"])
  | .node info kind children => do
      let si ← sourceInfoJson info
      let mut cs := #[]
      for child in children do cs := cs.push (← syntaxJson child)
      return arr [str "node",si,nameJson kind,.arr cs]
  | .atom info text => do
      let si ← sourceInfoJson info
      return arr [str "atom",si,str text]
  | .ident info raw value pre => do
      let si ← sourceInfoJson info
      let r ← rawSubstringJson raw
      return arr [str "ident",si,r,nameJson value,.arr (pre.map preresolvedJson).toArray]

def dataJson : DataValue → Build Json
  | .ofString x => pure (arr [str "string",str x])
  | .ofBool x => pure (arr [str "bool",toJson x])
  | .ofName x => pure (arr [str "name",nameJson x])
  | .ofNat x => pure (arr [str "nat",num x])
  | .ofInt x => pure (arr [str "int",toJson x])
  | .ofSyntax s => do pure (arr [str "syntax",← syntaxJson s])
'''
source=source.replace(anchor,anchor+extension)
source=source.replace('''          let j ← match dataJson v with
            | .ok j => pure j
            | .error message => throw message''','''          let j ← dataJson v''')
source=source.replace('("refs",toJson refs)]','("refs",toJson refs),("source_strings",toJson s.strings)]')
path=BUILD/'PostreleaseProducerAuditV2.lean'
assert not path.exists(),'preserve previous extended source'
path.write_text(source)
environment=dict(os.environ);environment['LEAN_PATH']=str(BUILD)
start=time.perf_counter()
p=subprocess.run([str(LEAN),'-o','PostreleaseProducerAuditV2.olean',path.name],cwd=BUILD,env=environment,
                 text=True,capture_output=True,timeout=60)
result={'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'seconds':time.perf_counter()-start,
        'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'timeout_seconds':60,
        'status':'PASS' if p.returncode==0 else 'FAIL','postcontact_extension':True}
out=HERE/'postrelease-v1-metadata-compile.json';assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','seconds','source_sha256')}))
raise SystemExit(p.returncode)
