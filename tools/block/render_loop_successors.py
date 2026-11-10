"""Render declarations only from frozen source-pass alternatives and Level 1 framing."""
from copy import deepcopy
from pathlib import Path
import argparse,hashlib,json,re,sys
parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);parser.add_argument('--source-receipt',type=Path,required=True);parser.add_argument('--source-receipt-sha256',required=True);parser.add_argument('--input-directory',type=Path,required=True);parser.add_argument('--coqc-args',type=Path,required=True);parser.add_argument('--function',default=None,help='function profile (default: decodeItem)');options=parser.parse_args()
B=Path('/home/cody/zesislar');W=Path(__file__).resolve().parents[2];R=Path(__file__).resolve().parent;O=options.output;O.mkdir(exist_ok=False)
sys.path.insert(0,str(W/'tools/block'))
from entry_formatter import SourceComponents,SymbolicConditions,format_entry_boundary
from fractional_source import FractionalSourceArrays,array_declaration
from render_support import component_source,definition_introduction_source,expression,identifier,unfold_declaration
from forward_resources import load_resource_vocabulary
from symbolic_state import Expr
from render_support import unfold_declaration
from boundary_guards import RocqContradictionCheck,contradictory_alternatives,refused_alternative_indices,require_complete_boundary,without_alternatives
from function_profiles import load_profile,loop_header
profile=load_profile(options.function);successors=profile['loop_successors'];continuation_id=successors['continuation_id']

def bind(p):p=Path(p);return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
forward=options.source_receipt; assert bind(forward)['sha256']==options.source_receipt_sha256, 'The loop source receipt changed'; packet=json.loads(forward.read_text()); data={'boundaries': []}
for suffix,head in successors['pairs']:
 alternatives=[]
 for index in range(successors['classes_per_head']):
  row=next(item for item in packet['rows'] if item['case']==head+'-'+str(index)); reportpath=Path(row['report']['path']); assert bind(reportpath)==row['report']; report=json.loads(reportpath.read_text()); boundary=next(item for item in report['boundaries'] if item['pc']==profile.pc(suffix)); assert boundary['status']=='generated'; require_complete_boundary(boundary); alternatives.extend(deepcopy(boundary['alternatives']))
 data['boundaries'].append({'pc':profile.pc(suffix),'status':'generated','alternatives':alternatives})
inputs=options.input_directory;vpath=inputs/'VOCABULARY-OLD.json';vocabulary=load_resource_vocabulary(vpath,bind(vpath)['sha256']);array=array_declaration(vocabulary)
shapes=json.loads((inputs/'SYSTEM-SHAPES.json').read_text())['rows'];system_binders=[{'name':Expr.from_dict(row['symbol']).value,'type':'bv '+str(row['width'])}for row in shapes if row['shape']in('mask','bits')]
pilots=[suffix for suffix,_ in successors['pairs']];cases=[];emitted=[]
header=loop_header(profile)
# These are the source-bound argument and continuation types from Level 1.
base_telescope=profile.telescope()
base_arguments=['args','returnAddress']
allowed_helpers={row['helper']['owner']+'.'+row['helper']['name']for row in vocabulary['rows']}
check=RocqContradictionCheck(json.loads(options.coqc_args.read_text()),header.split('\n',1)[1],O/'contradiction-checks')

for suffix in pilots:
 pc=profile.pc(suffix);index=next(i for i,b in enumerate(data['boundaries'])if b['pc']==pc);boundary=deepcopy(data['boundaries'][index]);name='fp_machineAt'+suffix;name=identifier(name,'generated entry');source_ref=str(forward)+'#source-derived-boundary/'+pc
 def provenance(*args,**kwargs):return {'source':source_ref}
 # Frame exactly the existing Level1 exit continuation outside every alternative.
 for alternative in boundary['alternatives']:
  resource=alternative['resource_boundary'];assert resource['tree']['right']=={'kind':'component','id':continuation_id}
  for component in resource['components']:
   if component['source']=='⌜domain args⌝':
    component['source']=profile['domain_component']
 def rendered(boundary):
  plain=SourceComponents({'K':{'owner':'parameter','name':'K'}},continuation_id=continuation_id,provenance=provenance)
  components=FractionalSourceArrays(plain,declaration=array);conditions=SymbolicConditions(provenance)
  formatted=format_entry_boundary(boundary,case_id=pc,source_policy='source-only',handwritten_owner='Level1.IslarisContractSpec',continuation_id=continuation_id,guard_scope=(0,),component_adapter=components,condition_adapter=conditions,helper_arguments=lambda body,context:list(base_arguments),scoped_binders=system_binders)
  record={'pc':pc,'source_boundary':source_ref,'alternative_count':len(boundary['alternatives']),'status':formatted.status,'manifest':formatted.manifest,'reports':formatted.reports,'guard_normalizations':conditions.normalizations,'fraction_applications':components.applications,'proof_ran':False}
  if formatted.response is None:return record,None,[]
  helpers={row['suffix']:name+'_'+row['suffix']for row in formatted.response['body']['additional_definitions']};facts=[]
  def render(node):
   kind=node['kind']
   if kind in('application','continuation'):
    reference=node['predicate'];arguments=node['arguments']
    if set(reference)=={'suffix'}:target=helpers[reference['suffix']]
    elif reference=={'owner':'parameter','name':'K'}:
     if kind!='continuation'or arguments:raise ValueError('The Level1 K parameter is applied or reinterpreted.')
     return 'K'
    else:
     target=reference['owner']+'.'+reference['name']
     if target not in allowed_helpers:raise ValueError('An application lacks a source-bound helper: '+target)
    return target+''.join(' ('+expression(argument,'application argument')+')'for argument in arguments)
   if kind=='pure':
    terms=[]
    for term in node['terms']:
     value=expression(term['term']['value'],'source-derived pure term');terms.append('('+value+')');facts.append({'term':value,'provenance':deepcopy(term['provenance'])})
    return '⌜'+' /\\ '.join(terms)+'⌝'
   if kind=='disjunction':return '('+' ∨ '.join('('+render(alt)+')'for alt in node['alternatives'])+')'
   return component_source(node,{}, {'source_hashes':{}}, W, None)
  def body_source(body):
   if body.get('lets')or body.get('loop'):raise ValueError('This source adapter has no let/loop declaration binding.')
   result='('+ ' ∗ '.join(render(component)for component in body['components'])+')'
   if body['existentials']:
    telescope=' '.join('('+identifier(binder['name'],'source existential')+' : '+expression(binder['type'],'source type')+')'for binder in body['existentials']);result='(∃ '+telescope+', '+result+')'
   return result
  definitions=[]
  for helper in formatted.response['body']['additional_definitions']:
   assert not next(row for row in formatted.manifest['helpers']if row['suffix']==helper['suffix'])['outer_binders']
   definition='Definition '+helpers[helper['suffix']]+base_telescope+' : iProp Sigma := '+body_source(helper['body'])+'%I.\n'
   definition_introduction_source(definition,helpers[helper['suffix']]);definitions.append((helpers[helper['suffix']],definition))
  definition='Definition '+name+base_telescope+' (K : iProp Sigma) : iProp Sigma := '+body_source(formatted.response['body'])+'%I.\n';definition_introduction_source(definition,name);definitions.append((name,definition))
  return record,definitions,facts
 refused_names=[]
 while True:
  record,definitions,facts=rendered(boundary)
  if definitions is None:break
  refused=contradictory_alternatives(definitions,check)
  if not refused:break
  refused_names.extend(refused);boundary=without_alternatives(boundary,refused_alternative_indices(refused))
 record['refused_alternatives']=refused_names
 if definitions is None:cases.append(record);continue
 module='Pilot'+suffix+'Entries';relative=Path(profile.generated_directory);directory=O/'sources'/relative;directory.mkdir(parents=True,exist_ok=True);entry=directory/(module+'.v');entry.write_text(header+'\n'.join(definition for _,definition in definitions))
 structural=directory/('Pilot'+suffix+'Structural.v');source=header+'Require Import '+'.'.join((relative/module).parts)+'.\n'
 for symbol,definition in definitions:source+=unfold_declaration(symbol, instance_name=symbol+'_unfold', locality='export')+definition_introduction_source(definition,symbol)+'\n'
 structural.write_text(source)
 for file in[entry,structural]:
  text=file.read_text();assert not re.search(r'\b(?:Proof|Qed|Admitted|Axiom|Ltac|Ltac2)\b',text)
 record.update(status='source_declarations_rendered',entry=bind(entry),structural=bind(structural),qualified_entry='.'.join((relative/module).parts)+'.'+name,definition_count=len(definitions),facts=facts,response=formatted.response,physical_declaration_check='pending',byte_identity_with_OLD='not_assumed')
 emitted.extend([bind(entry),bind(structural)]);cases.append(record)

(O/'RESULT.json').write_text(json.dumps({'status':'SOURCE_DECLARATIONS_ONLY','function':profile.name,'source_pass':bind(forward),'formatter_sources':[bind(W/'tools/block'/name)for name in['entry_formatter.py','guard_normal_form.py','coq_scopes.py','fractional_source.py']],'level1_K_source':bind(W/'ZesuSsz/Contracts/Level1.v'),'vocabulary':bind(vpath),'system_shapes':bind(inputs/'SYSTEM-SHAPES.json'),'cases':cases,'rendered_count':sum(c['status']=='source_declarations_rendered'for c in cases),'refused_count':sum(c['status']!='source_declarations_rendered'for c in cases),'sources':emitted,'proof_scripts_emitted':False,'new_native_calls':0,'native_release':False,'join_seeds_added':False,'contradiction_checks':check.runs},indent=2)+'\n')
print(json.dumps({'rendered':sum(c['status']=='source_declarations_rendered'for c in cases),'refused':[(c['pc'],c['reports'])for c in cases if c['status']!='source_declarations_rendered'],'result':bind(O/'RESULT.json')}))
