"""Authenticate individual outputs from one explicitly authorized closed failed run.

The context below exists only in the migration validator. It is not a READY
runtime and cannot authorize a prefix, proof, or arbitrary failed run.
"""
from pathlib import Path
from entry_chain import binding

KIND='accepted-closed-compilations'
LABEL='individual-successful-compilation-from-closed-failed-declaration-run'

def context(authority, reference, read):
 if authority.get('kind')!=KIND or authority.get('binding')!=reference:
  raise ValueError('The closed compilation origin is not authorized.')
 publication=read(reference)
 if publication.get('schema')!='entry-chain.closed-compilation-origin.v1' or publication.get('kind')!=KIND:
  raise ValueError('The closed compilation origin schema differs.')
 outer=read(publication['outer_runtime']);inner=read(publication['inner_runtime'])
 inventory=read(publication['binding_inventory']);index=read(publication['accepted_object_index'])['index'];snapshot=read(publication['compiler_snapshot']);read(publication['import_graph'])
 workspace=Path(publication['object_workspace']).resolve();compiler=publication['compiler']
 if (workspace!=Path(inner['job_output']).resolve()/'workspace' or
     publication['binding_inventory']!=inner['binding_inventory'] or
     publication['import_graph']!=inner['cache_import_graph'] or
     inner['physical_compiler']!=compiler or
     {k:snapshot['compiler'][k] for k in ['path','sha256']}!=compiler or
     snapshot['runtime']!=publication['inner_runtime'] or
     index['runtime']!=publication['inner_runtime'] or index['snapshot']!=publication['compiler_snapshot'] or
     index['producer']!=snapshot['producer'] or
     snapshot['mapping_context']['flags']!=inner['physical_flags'] or
     inner['module_files']!=outer['proof_runtime']['module_files']):
  raise ValueError('The closed compiler context, workspace, or inventory differs.')
 if binding(compiler['path'])!=compiler or publication['coqdep'] not in inventory['bindings']:
  raise ValueError('The closed compiler installation differs.')
 def normal(flags,root):return [word.replace(str(root),'{workspace}') for word in flags]
 if normal(inner['physical_flags'],workspace)!=normal(outer['physical_flags'],outer['prepared_workspace']):
  raise ValueError('The closed physical flags differ from the bound outer runtime.')
 rows=publication['successful_modules'];selected={row['module']:row for row in rows}
 refs={name:row['receipt'] for name,row in selected.items()}
 if (len(selected)!=len(rows) or refs!=authority.get('module_receipts') or
     sorted(index['receipts'],key=lambda row:row['path'])!=sorted(refs.values(),key=lambda row:row['path'])):
  raise ValueError('The closed object index differs from the exact authorized receipts.')
 result=read(publication['failed_result']);closure=read(publication['closure']);release=read(publication['release']);batch=read(publication['batch_identity']);final=read(publication['final_validation']);cpu=read(publication['CPU_final'])
 if (result.get('success') is not False or result.get('phase')!='prerequisites' or
     result.get('CPU')!=cpu or result.get('aggregate_peak_bytes')!=cpu.get('aggregate_peak_bytes') or
     final.get('runtime_sha256')!=publication['inner_runtime']['sha256'] or
     final.get('final_validation',{}).get('success') is not True or
     final['final_validation'].get('proof_bindings_checked',0)<=0 or
     closure.get('all_owned_actors_closed') is not True or not closure.get('actors') or
     any(actor.get('ended') is not True for actor in closure['actors']) or
     closure.get('batch_identity')!=batch or release.get('released') is not True or
     release.get('claim_key')!=closure.get('claim_key') or
     release.get('bytes')!=inner['canonical_admission']['minimum_claim_bytes'] or
     Path(batch['aggregate_path']).exists()):
  raise ValueError('The closed failed run lacks exact final validation or lifecycle evidence.')
 for key,name in [('failed_result','RESULT.json'),('closure','CLOSURE.json'),('release','RELEASE.json'),('CPU_final','CPU-FINAL.json'),('batch_identity','BATCH-IDENTITY.json')]:
  if Path(publication[key]['path'])!=Path(inner['job_output'])/name:
   raise ValueError('The closed lifecycle leaves its exact job.')
 for actor in closure['actors']+[closure['owner']]:
  try:
   fields=(Path('/proc')/str(actor['pid'])/'stat').read_text().rsplit(')',1)[1].split()
   if int(fields[19])==actor['startticks'] and fields[0] not in ['Z','X']:
    raise ValueError('A closed compilation actor is still active.')
  except FileNotFoundError:pass
 return {'prepared_workspace':str(workspace),'proof_runtime':{'module_files':inner['module_files']},
         'bindings':inventory['bindings'],'physical_flags':inner['physical_flags']},publication,selected,index

def selected_origin(authority, reference, module, source, obj, compiler, flags, workspace, read):
 config,publication,rows,index=context(authority,reference,read)
 if module not in rows:raise ValueError('The module lacks an authorized closed compilation.')
 row=rows[module];receipt=read(row['receipt']);old=Path(config['prepared_workspace'])
 if (receipt.get('schema')=='entry-chain.object-import-migration.v1' or
     receipt.get('successful_compilation') is not True or receipt.get('tool_result',{}).get('success') is not True or
     receipt.get('runtime')!=publication['inner_runtime'] or receipt.get('snapshot')!=publication['compiler_snapshot'] or
     receipt.get('producer')!=index['producer'] or receipt.get('compiler')!=publication['compiler'] or compiler!=publication['compiler'] or
     receipt.get('source')!=row['source'] or receipt.get('object')!=row['object'] or
     receipt.get('physical_result')!=row['physical_result'] or receipt.get('publication')!=row.get('publication') or
     Path(receipt['source']['path']).resolve()!=old/config['proof_runtime']['module_files'][module] or
     receipt.get('import_provenance',{}).get('module')!=module):
  raise ValueError('The individual closed compilation is incomplete or differs.')
 validation=read(receipt['import_provenance']['validation'])
 if validation.get('import_selection',{}).get('graph')!=publication['import_graph']:
  raise ValueError('The individual compilation names another import graph.')
 from object_imports import _record
 imports,recorded_workspace=_record(row['receipt'],module,source,obj,compiler,flags,Path(workspace).resolve())
 if recorded_workspace.resolve()!=old:
  raise ValueError('The individual closed compilation names another workspace.')
 from source_context import compilation
 effective=compilation(flags,binding(source))['physical_flags']
 return {'kind':LABEL,'publication':reference,'closed_runtime':publication['inner_runtime'],
         'original_receipts':[row['receipt']]},effective
