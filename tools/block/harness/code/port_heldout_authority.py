"""Authenticate run-2 descriptors before authorizing concrete stock callers."""

def validate(authority):
 from memory_policy import read
 rebind=read(authority['case_rebind']);transport=read(authority['eql18_targets']);targets=transport['cases']
 read(authority['frozen_manifest'])
 read(authority['declaration_evidence'])
 if (rebind['frozen_manifest']!=authority['frozen_manifest'] or
     transport['frozen_CASES']!=authority['frozen_manifest'] or
     transport['declaration_evidence']!=authority['declaration_evidence']):
  raise ValueError('The held-out frozen manifest differs.')
 rows=rebind['cases'];by={row['casekey']:row for row in targets}
 if len(rows)!=78 or len(by)!=18 or len(targets)!=18:
  raise ValueError('The held-out descriptor or transport count differs.')
 inventory=[];cases=[]
 for row in rows:
  source=row['frozen_case'];key=row['case_id']
  pc=int(source['pc'],0) if isinstance(source['pc'],str) else source['pc']
  if source['case_id']!=key or source['native_tactic']!='zesu_block.' or source['statement_sha256']!=row['statement_sha256']:
   raise ValueError('A held-out descriptor changed its stock boundary.')
  inventory.append(dict(block=key,pc=pc,statement_sha256=row['statement_sha256'],
                        ordered_edges_sha256=row['ordered_edges_sha256'],score_group=source['score_group'],
                        transport='ready' if key in by else 'pending'))
  if key in by:
   target=by[key]
   caller=dict(path=target['path'],sha256=target['hash'])
   if (source['caller']!=caller or source['caller_module']!=target['module'] or
       source['statement_sha256']!=target['statementhash'] or pc!=int(target['pc'],0) or
       target['native_job_key']!=format(pc,'x')):
    raise ValueError('A held-out caller differs from its frozen boundary.')
   cases.append(dict(block=target['native_job_key'],module=target['module'],source=caller,
                     statement_sha256=target['statementhash'],pc=pc))
  elif source['caller'] is not None or source.get('native_caller_transport_pending') is not True:
   raise ValueError('A held-out pending transport changed.')
 if (authority.get('inventory')!=inventory or authority.get('cases')!=cases or
     len({row['block'] for row in inventory})!=78 or len({row['pc'] for row in inventory})!=78 or
     authority.get('descriptor_count')!=78 or authority.get('executable_case_count')!=18 or
     authority.get('transport_pending_count')!=60 or authority.get('blind_reporting') is not True):
  raise ValueError('The held-out inventory differs from its exact transports.')
 return authority
