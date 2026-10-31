"""Preserve an explicit post-import scratch caller without changing its proof."""
from pathlib import Path

def install_rules_import(path,module,read_statement,native_route=None):
 path=Path(path);original=path.read_text();line='Require Import '+module+'.';rows=original.splitlines(keepends=True);matches=[i for i,row in enumerate(rows) if row.strip()==line]
 if len(matches)>1:raise ValueError('The native source repeats its scratch rules import.')
 before=read_statement(path)
 if native_route:
  from native_route import authority
  import hashlib
  if len(matches)!=1:raise ValueError('The minimal caller must contain exactly one explicit scratch rules import.')
  packet=authority(native_route)
  if hashlib.sha256(path.read_bytes()).hexdigest()!=packet['native_source']['sha256']:raise ValueError('The minimal caller differs from its bound source.')
  if module!=packet['tactic_source']['module']:raise ValueError('The minimal rules import differs from its authority.')
  if before['native_body']!=packet['native_body']:raise ValueError('The minimal native command differs from its authority.')
  if read_statement(path)!=before:raise ValueError('The minimal import check changed its statement or command.')
  return {'placement':'authority_explicit_import_preserved','source_unchanged':True,'statement_unchanged':True,'native_command_unchanged':True}
 if matches and matches[0]!=0:
  if not original.startswith('Require Import ZesuSsz.Automation.All.\n'):raise ValueError('The native source must start with Automation.All.')
  return {'placement':'existing_post_import_preserved','source_unchanged':True}
 clean=''.join(row for i,row in enumerate(rows) if i not in matches)
 if not clean.startswith('Require Import ZesuSsz.Automation.All.\n'):raise ValueError('The native source must start with Automation.All.')
 path.write_text(clean);spec=read_statement(path);offset=len(spec['prefix'])+len(spec['statement'])+len(spec.get('pre_proof_commands',''))
 if clean[offset:offset+6]!='Proof.':raise ValueError('The scratch import frontier is not the original Proof sentence.')
 path.write_text(clean[:offset]+line+'\n'+clean[offset:]);after=read_statement(path)
 if after['statement']!=before['statement'] or after['native_body']!=before['native_body']:raise ValueError('The scratch import changed the statement or native command.')
 return {'placement':'after_existing_imports','statement_unchanged':True,'native_command_unchanged':True}
