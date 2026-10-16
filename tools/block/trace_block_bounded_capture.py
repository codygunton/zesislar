"""Validate bounded displays and complete term references from one sealed capture."""
from collections.abc import Mapping
from trace_block_kernel_display import (MetadataEvidence, verify_kernel_display, verify_kernel_capture_reload, artifact,
    _fields, _same, _exact, _integer, _array, _bounded_text)


def pointer(name):
    return '#/displays/' + name.replace('~','~0').replace('/','~1')


def _term(value, sidecar, name):
    _fields(value,'availability complete_sidecar node_ref')
    _same(value,'availability','referenced')
    _same(value,'complete_sidecar',sidecar)
    _same(value,'node_ref',{'root_id':name,'child_path':[]})


class BoundedCapture:
    """The caller seals every artifact and supplies exact reader/runtime identities."""
    def __init__(self, metadata, capture, *, sequence, expected_reader,
                 expected_toolchain_ref, expected_marker_plan, expected_arguments):
        self.metadata,self.capture=metadata,capture
        version=capture.get('schema')
        if type(version)is not int or version not in (1,2):raise ValueError('The bounded capture schema is unsupported.')
        fields='schema surface_policy event_sequence notation no_notation evars evar_catalog_ref '
        fields+='complete_sidecar reload_evidence fresh_evar_counter live_goal_ids displays show_proof'
        _fields(capture,fields+(' group_policy group_counts'if version==2 else''))
        _same(capture,'surface_policy','bounded-kernel-v1')
        if version==2:
            _same(capture,'group_policy','raw-ordered-goals-v1')
            _fields(capture['group_counts'],'goals shelf given_up')
            for group in ('goals','shelf','given_up'):_integer(capture['group_counts'][group])
        _same(capture,'event_sequence',sequence);_integer(sequence,1)
        _integer(capture['fresh_evar_counter'])
        self.sidecar=capture['complete_sidecar'];self.catalog_ref=capture['evar_catalog_ref']
        artifact(metadata.root,self.sidecar);artifact(metadata.root,self.catalog_ref)
        self.catalog=metadata.read(self.catalog_ref)
        _fields(self.catalog,'schema complete_sidecar entries');_same(self.catalog,'schema',1)
        _same(self.catalog,'complete_sidecar',self.sidecar)
        if not isinstance(capture['displays'],Mapping):raise ValueError('The capture lacks its exact display map.')
        if version==2:
            verify_kernel_capture_reload(MetadataEvidence(metadata),capture,
                expected_reader=expected_reader,expected_toolchain_ref=expected_toolchain_ref,
                expected_marker_plan=expected_marker_plan,expected_arguments=expected_arguments)
        self.displays=capture['displays'];self.checked={};self.used=set()
        for name,display in self.displays.items():
            _same(display,'root_id',name);_same(display,'complete_sidecar',self.sidecar)
            _same(display,'evar_catalog_ref',self.catalog_ref)
            _same(display,'reload_evidence',capture['reload_evidence'])
            self.checked[name]=verify_kernel_display(MetadataEvidence(metadata),display,
                expected_reader=expected_reader,expected_toolchain_ref=expected_toolchain_ref,
                expected_marker_plan=expected_marker_plan,expected_arguments=expected_arguments)
        if version==1 and not self.checked:raise ValueError('The capture has no verified printed root.')
        plan=metadata.read(expected_marker_plan)
        descriptor=metadata.read(plan['context_ref'])
        _fields(descriptor,'schema kind complete_sidecar goals shelf given_up')
        _same(descriptor,'schema',1);_same(descriptor,'kind','kernel-snapshot-context')
        _same(descriptor,'complete_sidecar',self.sidecar)
        self._evars()
        self.groups={name:self._goals(name)for name in ('goals','shelf','given_up')}
        if not _exact(capture['live_goal_ids'],[row['id']for row in self.groups['goals']]):
            raise ValueError('The capture goal list differs from its live goal identities.')
        for mode in ('notation','no_notation'):
            _same(capture[mode],'hidden_stack',{'availability':'unavailable',
                'reason':'The public API does not expose ordered hidden focus frames'})
        for group in ('goals','shelf','given_up'):
            _same(descriptor,group,[row['id']for row in self.groups[group]])
        self.proof=self._proof()
        if self.used!=set(self.displays):raise ValueError('The capture has an unassociated display root.')

    def _display(self,name,reference,left,right):
        if name not in self.displays or reference!=pointer(name):
            raise ValueError('The term lacks its exact display pointer.')
        display=self.displays[name]
        if not _exact(left,display['goal']) or not _exact(right,display['goal_nonotation']):
            raise ValueError('The bounded text differs from its verified display pair.')
        self.used.add(name)
        return {'surface_policy':'bounded-kernel-v1','display_ref':reference,
                'complete_sidecar':self.sidecar,'node_ref':display['node_ref'],
                'display_input_ref':display['display_input_ref'],
                'root_reload_evidence':display['root_reload_evidence'],
                'printed_text':'bounded','complete_term':'marshal-reload-and-membership-verified'}

    def _evars(self):
        raw,compact=self.catalog['entries'],self.capture['evars']
        if not _array(raw)or not _array(compact)or len(raw)!=len(compact):
            raise ValueError('The compact evar map differs from its complete catalog.')
        self.entries=[];self.by_id={};self.catalog_indexes={}
        for index,(entry,value)in enumerate(zip(raw,compact)):
            _fields(entry,'id name defined type body context context_declarations filter candidates candidate_count')
            _fields(value,'id defined type body context entry_ref')
            key=entry['id'];_integer(key)
            if key in self.by_id:raise ValueError('The complete evar catalog repeats an identity.')
            if type(entry['defined'])is not bool:raise ValueError('The evar status is not Boolean.')
            for field in ('id','defined','body'):_same(value,field,entry[field])
            for field,suffix in [('entry_ref',''),('context','/context')]:
                _same(value,field,{'catalog_ref':self.catalog_ref,'pointer':'#/entries/%d'%index+suffix})
            stem='evar/%d/'%key
            if entry['defined']:
                _fields(value['type'],'availability reason');_fields(entry['type'],'availability reason')
                _same(value['type'],'availability','unavailable');_same(entry['type'],'availability','unavailable')
                _same(value['type'],'reason','Evd erases defined conclusions')
                _same(entry['type'],'reason','Evd erases the conclusion of a defined evar')
                _term(value['body'],self.sidecar,stem+'body')
            else:
                _same(value,'type',entry['type']);_term(entry['type'],self.sidecar,stem+'conclusion')
                if entry['body']is not None:raise ValueError('An undefined evar has a defined body.')
            context=entry['context'];filters=entry['filter']
            if not _array(context)or not _array(filters)or any(type(v)is not bool for v in filters):
                raise ValueError('The catalog lacks its exact context or filter.')
            _same(entry,'context_declarations',len(context))
            if len(filters)!=len(context):raise ValueError('The context filter has a different length.')
            root=stem+('body'if entry['defined']else'conclusion')
            for n,declaration in enumerate(context):
                _fields(declaration,'name type body')
                if not isinstance(declaration['name'],str):raise ValueError('A context binder lacks its exact name.')
                _term(declaration['type'],self.sidecar,root+'@named:%d:type'%n)
                if declaration['body']is not None:_term(declaration['body'],self.sidecar,root+'@named:%d:body'%n)
            candidates=entry['candidates']
            if candidates is None:
                if entry['candidate_count']is not None:raise ValueError('An absent candidate list has a count.')
            else:
                if not _array(candidates):raise ValueError('The catalog candidates are not ordered.')
                _same(entry,'candidate_count',len(candidates))
                for n,term in enumerate(candidates):_term(term,self.sidecar,stem+'candidate/%d'%n)
            self.by_id[key]=entry;self.catalog_indexes[key]=index
            self.entries.append({'id':key,'name':entry['name'],'status':'defined'if entry['defined']else'undefined',
                'type':value['type'],'body':value['body'],'context':value['context'],'entry_ref':value['entry_ref'],
                'filter':filters,'candidates':candidates})

    def _goals(self,group):
        for mode in ('notation','no_notation'):
            _fields(self.capture[mode],'goals shelf given_up hidden_stack')
        left,right=self.capture['notation'][group],self.capture['no_notation'][group]
        if not _array(left)or not _array(right)or len(left)!=len(right):raise ValueError('The goal printers differ in group size.')
        version=self.capture.get('schema',1)
        if version==2:
            _same(self.capture['group_counts'],group,len(left))
        rows=[];seen=set()
        for a,b in zip(left,right):
            for goal in (a,b):_fields(goal,'evar name conclusion display_ref hyps'+(' status entry_ref body'if version==2 else''))
            key=a['evar'];_integer(key)
            if key not in self.by_id or(version==1 and(key in seen or self.by_id[key]['defined'])):
                raise ValueError('A goal lacks its exact supported catalog entry.')
            seen.add(key)
            _same(a,'name',self.by_id[key]['name'])
            for field in ('evar','name','display_ref'):_same(b,field,a[field])
            defined=self.by_id[key]['defined']
            if version==2:
                for mode in (a,b):
                    _same(mode,'status','defined'if defined else'undefined')
                    _same(mode,'entry_ref',{'catalog_ref':self.catalog_ref,'pointer':'#/entries/%d'%self.catalog_indexes[key]})
                    _same(mode,'body',self.by_id[key]['body'])
            if defined:
                for mode in (a,b):
                    _same(mode,'conclusion',{'availability':'unavailable','reason':'Evd erases the conclusion of a defined evar'})
                    _same(mode,'display_ref',None)
                _term(a['body'],self.sidecar,'evar/%d/body'%key)
                term=None
            else:
                term=self._display('evar/%d/conclusion'%key,a['display_ref'],a['conclusion'],b['conclusion'])
            hyps=[];lh,rh=a['hyps'],b['hyps'];context=self.by_id[key]['context']
            visible=[index for index,enabled in enumerate(self.by_id[key]['filter'])if enabled]
            visible.reverse()
            if not _array(lh)or not _array(rh)or len(lh)!=len(rh)or len(lh)!=len(visible):
                raise ValueError('The printed context differs from the complete catalog.')
            for n,(x,y)in enumerate(zip(lh,rh)):
                for hyp in (x,y):_fields(hyp,'names type type_display_ref body body_display_ref')
                for field in ('names','type_display_ref','body_display_ref'):_same(y,field,x[field])
                index=visible[n];declaration=context[index]
                _same(x,'names',[declaration['name']])
                stem='evar/%d/hyp/%d/'%(key,index)
                type_ref=self._display(stem+'type',x['type_display_ref'],x['type'],y['type'])
                body_ref=None
                if declaration['body']is None:
                    if any(z[f]is not None for z in (x,y)for f in ('body','body_display_ref')):
                        raise ValueError('An assumption has a printed definition body.')
                else:body_ref=self._display(stem+'body',x['body_display_ref'],x['body'],y['body'])
                hyps.append({'names':x['names'],'type':x['type'],'type_nonotation':y['type'],
                             'body':x['body'],'body_nonotation':y['body'],'type_term':type_ref,'body_term':body_ref})
            row={'id':key,'goal':None if defined else a['conclusion'],
                 'goal_nonotation':None if defined else b['conclusion'],'hyps':hyps,'term':term}
            if version==2:
                row.update(name=a['name'],status=a['status'],entry_ref=a['entry_ref'],body=a['body'],
                    goal_availability=a['conclusion']if defined else{'availability':'bounded-display'})
            rows.append(row)
        return rows

    def _proof(self):
        proof=self.capture['show_proof'];_fields(proof,'availability command notation no_notation complete_sidecar')
        _same(proof,'command','Show Proof.');_same(proof,'complete_sidecar',self.sidecar)
        left,right=proof['notation'],proof['no_notation']
        if not _array(left)or not _array(right)or len(left)!=len(right):raise ValueError('The partial proof printers differ.')
        if proof['availability']=='not-requested':
            if left or right:raise ValueError('An unrequested proof has printed terms.')
        elif proof['availability']=='bounded-display':
            if not left:raise ValueError('The requested partial proof has no term.')
            for n,(a,b)in enumerate(zip(left,right)):self._display('proof/%d'%n,pointer('proof/%d'%n),a,b)
        else:raise ValueError('The partial proof availability is unsupported.')
        return proof

    def stable(self):
        primary=self.groups['goals'][0]if self.groups['goals']else None
        result={'surface_policy':'bounded-kernel-v1','goal':primary['goal']if primary else None,
            'goal_nonotation':primary['goal_nonotation']if primary else None,'hyps':primary['hyps']if primary else [],
            'current_goals':self.groups['goals'],'shelf':self.groups['shelf'],'given_up':self.groups['given_up'],
            'evars':{'availability':'complete-referenced','entries':self.entries,'catalog_ref':self.catalog_ref,
                     'defined_conclusion_types':'unavailable: Evd erases defined conclusions'},
            'complete_sidecar':self.sidecar,'reload_evidence':self.capture['reload_evidence'],
            'displays':self.displays,'show_proof':self.proof,'fresh_evar_counter':self.capture['fresh_evar_counter'],
            'hidden_focus_frames':self.capture['notation']['hidden_stack'],
            'serialization_scope':{
                'kernel_roots':'Complete referenced Marshal terms and local contexts.',
                'universe_state':'Present in the Marshal snapshot. No independent semantic check.',
                'evar_relevance':'Present in the Marshal catalog. Not separately exposed in JSON.',
                'evar_source':'unavailable', 'evar_abstraction':'unavailable',
                'defined_conclusion_types':'unavailable: Evd erases defined conclusions',
                'receipt_scope':'Serialization preservation. No kernel typecheck or semantic-equivalence claim.'},
            'completeness':{'printed_terms':'bounded','complete_terms':'marshal-reload-and-membership-verified',
                            'session_and_coverage':'caller-prerequisite'}}
        if self.capture['schema']==2:
            result.update(group_policy=self.capture['group_policy'],group_counts=self.capture['group_counts'],
                goal_availability=primary['goal_availability']if primary else{'availability':'no-raw-goal'})
        return result
