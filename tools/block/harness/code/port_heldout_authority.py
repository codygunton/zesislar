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
 raw_by={}
 if 'raw60_targets' in authority:
  raw=read(authority['raw60_targets'])
  read(authority['raw60_emission']);read(authority['raw60_refusal_checks'])
  raw_by={row['casekey']:row for row in raw['cases']}
  if (raw['frozen_CASES']!=authority['frozen_manifest'] or
      raw['caller_emission']!=authority['raw60_emission'] or
      raw['corrected_refusal_checks']!=authority['raw60_refusal_checks'] or
      raw.get('case_count')!=60 or raw.get('ordered_edges')!=103 or
      sum(len(row['ordered_source_edges']) for row in raw['cases'])!=103 or
      len(raw['cases'])!=60 or set(raw_by)!={row['case_id'] for row in rows[18:]} or
      set(raw_by)&set(by)):
   raise ValueError('The held-out raw transports differ from their frozen inventory.')
  by.update(raw_by)
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
   if key in raw_by:
    if (source['caller'] is not None or source.get('native_caller_transport_pending') is not True or
        target['frozen_case']!=source or target['ordered_source_edges']!=source['CFG_successors'] or
        target['protected_interval']['sha256']!=row['statement_sha256']):
     raise ValueError('A held-out raw transport changes frozen bytes or ordered edges.')
   elif source['caller']!=caller or source['caller_module']!=target['module']:
    raise ValueError('A held-out caller differs from its frozen boundary.')
   if (source['statement_sha256']!=target['statementhash'] or pc!=int(target['pc'],0) or
       target['native_job_key']!=format(pc,'x')):
    raise ValueError('A held-out caller differs from its frozen boundary.')
   cases.append(dict(block=target['native_job_key'],module=target['module'],source=caller,
                     statement_sha256=target['statementhash'],pc=pc))
  elif source['caller'] is not None or source.get('native_caller_transport_pending') is not True:
   raise ValueError('A held-out pending transport changed.')
 case_count=78 if raw_by else 18
 if (authority.get('inventory')!=inventory or authority.get('cases')!=cases or
     len({row['block'] for row in inventory})!=78 or len({row['pc'] for row in inventory})!=78 or
     authority.get('descriptor_count')!=78 or authority.get('executable_case_count')!=case_count or
     authority.get('transport_pending_count')!=78-case_count or authority.get('blind_reporting') is not True):
  raise ValueError('The held-out inventory differs from its exact transports.')
 return authority
