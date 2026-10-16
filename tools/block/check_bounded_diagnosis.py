"""Check bounded diagnosis citations against complete, sealed term evidence.

Printed goal text remains bounded. This route checks retained Marshal reload
receipts and artifact membership. It makes no new kernel-equivalence claim.
The legacy checker remains unchanged. This route checks named-rule terminal evidence.
"""
from collections.abc import Mapping
from contextlib import ExitStack
import argparse
import json
from pathlib import Path
import re
import types

import check_diagnosis as legacy
from trace_block import logical_session_id
from trace_block_bounded_aliases import (AliasDocument, verify_aliases,
                                         verify_alias_files)
from trace_block_bounded_projection import ProjectionView
from trace_block_kernel_display import artifact
from trace_block_seal import file_sha256, verify_root_seal


class BoundedDiagnosisError(legacy.DiagnosisError):
    """The bounded citation lacks its exact retained evidence."""


def require(condition, message):
    if not condition:
        raise BoundedDiagnosisError(message)


def file_reference(path, reference):
    """Check exact file bytes before interpreting any referenced JSON."""
    path = Path(path).resolve(strict=True)
    require(isinstance(reference, Mapping)
            and set(reference) == {'path', 'sha256', 'bytes'},
            'The evidence file reference has unsupported fields.')
    require(Path(reference['path']).resolve(strict=True) == path,
            'The evidence reference names another file.')
    require(type(reference['bytes']) is int and reference['bytes'] >= 0,
            'The evidence byte count is invalid.')
    require(path.is_file() and path.stat().st_size == reference['bytes']
            and file_sha256(path) == reference['sha256'],
            'The referenced evidence bytes changed.')
    return path


class CheckedBundle:
    """Keep all lazy readers open while citation and state checks use them.

    The caller supplies a sealed map hash and an independently bound request.
    The accepted projection checks exact reader, toolchain, root, context,
    catalog, invocation, and reload associations for every complete term.
    """
    def __init__(self, directory, *, expected_map_sha256, expected_request,
                 index_dir):
        self.directory = Path(directory).resolve(strict=True)
        self.index_dir = Path(index_dir).absolute()
        require(not self.index_dir.resolve().is_relative_to(self.directory),
                'Diagnosis indexes must remain outside the sealed bundle.')
        self.stack = ExitStack()
        try:
            require(isinstance(expected_map_sha256, str)
                    and re.fullmatch('[0-9a-f]{64}', expected_map_sha256),
                    'The caller must bind the exact evidence map hash.')
            map_path = self.directory / 'EVIDENCE-MAP.json'
            require(file_sha256(map_path) == expected_map_sha256,
                    'The evidence map differs from its external binding.')
            self.mapping = json.loads(map_path.read_text())
            m = self.mapping
            require(type(m.get('schema')) is int and m['schema'] == 1
                    and m.get('surface_policy') == 'bounded-kernel-v1',
                    'The bundle does not use the bounded surface policy.')
            trace_path = self.directory / 'TRACE.json'
            file_reference(trace_path, m['outputs']['TRACE.json'])
            file_reference(self.directory / 'TRACE.md', m['outputs']['TRACE.md'])
            self.document = json.loads(trace_path.read_text())
            for name, reference in m['projection_sources'].items():
                require(Path(reference['path']).name == name,
                        'A producer source reference has another module name.')
                file_reference(Path(reference['path']), reference)
            self.session = logical_session_id(expected_request)
            require(m['session'] == self.session
                    and self.document['session']['id'] == self.session,
                    'The bundle belongs to another logical session.')
            self.raw_root = Path(m['raw_root']).resolve(strict=True)
            self.evidence = self.raw_root / 'evidence'
            require(not self.index_dir.resolve().is_relative_to(self.raw_root),
                    'Diagnosis indexes must remain outside the raw evidence.')
            require(not self.index_dir.exists(), 'Diagnosis indexes require a fresh private directory.')
            require(Path(m['evidence_link']).absolute() == self.directory / 'evidence'
                    and (self.directory / 'evidence').resolve(strict=True) == self.evidence
                    and Path(m['evidence_target']).resolve(strict=True) == self.evidence,
                    'The bundle evidence path targets another raw directory.')
            request_path = file_reference(self.evidence / 'REQUEST.json', m['request'])
            request = json.loads(request_path.read_text())
            self.request = request
            require(request == expected_request,
                    'The retained request differs from the caller binding.')
            file_reference(self.evidence / 'SESSION.json', m['runtime_session'])
            seal = file_reference(self.directory / 'RAW-SEAL.json', m['raw_seal'])
            self.raw_verification = verify_root_seal(self.evidence, self.session, seal)
            require(self.raw_verification == m['raw_verification'],
                    'The raw seal differs from its recorded verification.')
            alias_dir = self.directory / 'aliases'
            require(Path(m['alias_directory']).resolve(strict=True) == alias_dir,
                    'The alias directory leaves this exact bundle.')
            verify_alias_files(alias_dir, m['alias_binding']['files'])
            aliases = self.stack.enter_context(AliasDocument(alias_dir,
                m['alias_binding']['artifact'], index_dir=self.index_dir / 'aliases'))
            self.view = self.stack.enter_context(ProjectionView(request, self.evidence,
                index_dir=self.index_dir / 'projection'))
            verification = verify_aliases(self.document, aliases,
                                           self.view.trace, self.evidence)
            require(verification == m['alias_verification'],
                    'The alias verification differs from its checked projection.')
            require(m['outputs']['TRACE.json']['sha256'] == verification['trace_sha256']
                    and m['alias_binding']['logical_sha256'] == verification['alias_map_sha256'],
                    'The stable output and alias seal do not agree.')
            index = file_reference(self.directory / 'raw/INDEX.json', m['raw_index'])
            rebuilt_index = self.index_dir / 'REBUILT-INDEX.json'
            self.view.write_raw_index(rebuilt_index)
            require(file_sha256(index) == file_sha256(rebuilt_index),
                    'The raw index differs from the checked projection.')
            self.alias_mapping = aliases
            self.aliases = {row['name']: row['reference'] for row in aliases['aliases']}
            self.trace_path = trace_path
            self.owned_captures = {}
            for value in self.document['points']:
                self.owned_captures[id(value)] = value
            if self.document.get('residual') is not None:
                value = self.document['residual']
                self.owned_captures[id(value)] = value
            for value in self.document['snapshots'].values():
                self.owned_captures[id(value)] = value
            for value in self.owned_captures.values():
                self.check_capture(value, self.session)
            self.verification = verification
            self._after_check()
        except BaseException:
            self.close()
            raise

    def __enter__(self):
        return self

    def __exit__(self, *arguments):
        try:
            if arguments[0] is None:
                self._after_check()
        finally:
            self.close()

    def close(self):
        self.stack.close()

    def _after_check(self):
        require(verify_aliases(self.document, self.alias_mapping, self.view.trace,
                              self.evidence) == self.verification,
                'The in-memory citation document changed after alias validation.')
        require(verify_root_seal(self.evidence, self.session,
                    Path(self.mapping['raw_seal']['path'])) == self.raw_verification,
                'The raw evidence changed during diagnosis validation.')
        file_reference(self.trace_path, self.mapping['outputs']['TRACE.json'])
        verify_alias_files(self.directory / 'aliases', self.mapping['alias_binding']['files'])

    def reference(self, value):
        require(isinstance(value, Mapping) and set(value) == {'artifact'}
                and isinstance(value['artifact'], str),
                'The term lacks an exact logical artifact pointer.')
        tokens = legacy.pointer_tokens(value['artifact'][1:]) if value['artifact'].startswith('#') else []
        require(len(tokens) == 2 and tokens[0] == 'artifacts'
                and tokens[1] in self.aliases,
                'The logical artifact pointer does not resolve.')
        reference = self.aliases[tokens[1]]
        artifact(self.evidence, reference)
        return reference

    def check_capture(self, value, session):
        require(id(value) in self.owned_captures
                and self.owned_captures[id(value)] is value,
                'The cited capture is outside the checked bounded projection.')
        require(session == self.session and value.get('session_id', session) == session,
                'The cited capture belongs to another logical session.')
        require(value.get('surface_policy') == 'bounded-kernel-v1'
                and value.get('evars', {}).get('availability') == 'complete-referenced',
                'The cited state lacks its complete referenced evar catalog.')
        require(value.get('completeness', {}).get('printed_terms') == 'bounded'
                and value['completeness'].get('complete_terms') == 'marshal-reload-and-membership-verified',
                'The cited state lacks checked complete term references.')
        self.reference(value['complete_sidecar'])
        for name in ('hyps', 'current_goals', 'shelf', 'given_up'):
            require(isinstance(value.get(name), list), 'The bounded capture lacks its ' + name + ' list.')

    def state_key(self, value):
        self.check_capture(value, self.session)
        reference = self.reference(value['complete_sidecar'])
        return (reference['sha256'], reference['bytes'], value['fresh_evar_counter'],
                tuple(tuple(row['id'] for row in value[group])
                      for group in ('current_goals', 'shelf', 'given_up')))

    def same_state(self, left, right):
        """Require identical complete serialization, not equivalent display text."""
        return self.state_key(left) == self.state_key(right)

    def refusal_observation(self, document, fragment):
        require(document is self.document, 'The refusal names another checked document.')
        tokens = legacy.pointer_tokens(fragment)
        if len(tokens) == 5 and tokens[0] == 'points':
            prefix, tail = '/points/' + tokens[1], tokens[2:]
        elif len(tokens) == 4 and tokens[0] == 'residual':
            prefix, tail = '/residual', tokens[1:]
        else:
            raise BoundedDiagnosisError('Cite one exact bounded refusal field.')
        require(tail[0] == 'refusal' and tail[2] in {'message', 'clause'},
                'Cite the exact refusal message or exposed clause.')
        point = legacy.resolve_pointer(document, prefix)
        self.check_capture(point, self.session)
        refusal = legacy.resolve_pointer(document, prefix + '/refusal/' + tail[1])
        require(isinstance(refusal, dict) and isinstance(refusal.get('message'), str)
                and refusal['message'].strip(), 'The refusal lacks its exact message.')
        require(refusal.get('exposure') in {'exposed', 'not-exposed'},
                'The refusal lacks its exposure status.')
        index = refusal.get('hand_call_index')
        require(type(index) is int and 0 <= index < len(point['hand_call']),
                'The refusal lacks its exact trial association.')
        trial = point['hand_call'][index]
        required = {'before', 'after_trial', 'rollback', 'rollback_equal', 'command',
                    'clause', 'feedback', 'outcome'}
        require(isinstance(trial, dict) and required.issubset(trial)
                and isinstance(trial['command'], str) and trial['command'].strip(),
                'The refused trial lacks its recorded command or snapshots.')
        require(all(trial[name] is not None for name in ('before', 'after_trial', 'rollback', 'feedback'))
                and trial['outcome'] == 'refused' and trial['rollback_equal'] is True
                and trial['clause'] == refusal.get('clause'),
                'The refusal differs from its trial or exact rollback record.')
        return {'point': point, 'refusal': refusal, 'trial': trial}

    def resolve(self, pointer):
        value = legacy.resolve_pointer(self.document, pointer)
        reference = None
        if isinstance(value, Mapping) and set(value) == {'artifact'}:
            reference = self.reference(value)
        return {'value': value, 'referenced_artifact': reference,
                'printed_text': 'bounded', 'complete_terms': 'checked-retained-Marshal-evidence',
                'scope': 'Serialization preservation. No new kernel typecheck or semantic-equivalence claim.'}

    def terminal_rule_success(self, document, trial_pointer, expected_rule, citations):
        """Check the exact terminal occurrence without changing a TRACE verdict."""
        from trace_block_bounded_success import rule_success
        require(document is self.document, 'The terminal claim names another checked bundle.')
        tokens = legacy.pointer_tokens(trial_pointer)
        require(len(tokens) == 4 and tokens[0] == 'points' and tokens[2] == 'hand_call',
                'The terminal claim must name an exact rule-entry trial.')
        require(re.fullmatch('0|[1-9][0-9]*', tokens[1])
                and re.fullmatch('0|[1-9][0-9]*', tokens[3]),
                'The terminal occurrence index is invalid.')
        point_index, trial_index = int(tokens[1]), int(tokens[3])
        raw = self.view.trace
        point = raw['points'][point_index]
        descriptor = self.request['entry_descriptors'][point['trigger']['client']]
        require(descriptor['rule'] == expected_rule,
                'The terminal rule differs from the diagnosed rule.')
        certificate = rule_success(point, raw['snapshots'], descriptor['commands']['whole-rule'],
            self.session, expected_rule=expected_rule, trial_index=trial_index)
        require(certificate is not None,
                'The exact whole-rule trial lacks complete named-rule terminal evidence.')
        trial = document['points'][point_index]['hand_call'][trial_index]
        direct = [tokens, tokens + ['outcome'],
                  tokens + ['commands', str(len(trial['commands']) - 1), 'outcome']]
        supported = any(pointer in direct for pointer, _ in citations)
        certificate_pointer = ['points', str(point_index), 'rule_success']
        raw_certificate = point.get('rule_success')
        if raw_certificate == certificate:
            supported = supported or any(pointer == certificate_pointer for pointer, _ in citations)
        verdict = document['verdict']
        if any(pointer in (['verdict'], ['verdict', 'status'], ['verdict', 'evidence'])
               for pointer, _ in citations):
            if verdict.get('status') == 'actual-success' and verdict.get('session') == self.session:
                if verdict.get('kind') == 'rule_success':
                    supported = supported or (raw_certificate == certificate
                        and verdict.get('rule') == expected_rule
                        and verdict.get('evidence') == '#/' + '/'.join(certificate_pointer))
                elif verdict.get('kind') == 'proof_closure':
                    supported = supported or document['completion'].get('proof_closed') is True
        require(supported, 'The terminal row lacks its exact successful rule evidence.')
        return certificate

    def semantic_violations(self, rows, base):
        """Use the legacy cycle rules with checked named-rule terminal evidence.

        The cycle helpers share code with the legacy checker. Bounded capture
        ownership, full-byte state joins, and named-rule terminal checks differ.
        This operation never changes a legacy module global or acceptance mode.
        """
        namespace = dict(vars(legacy))
        namespace.update(check_capture=self.check_capture,
                         refusal_observation=self.refusal_observation,
                         same_state=self.same_state)
        for name in ('snapshot', 'command_observation'):
            function = getattr(legacy, name)
            namespace[name] = types.FunctionType(function.__code__, namespace,
                function.__name__, function.__defaults__, function.__closure__)
        function = _bounded_semantic_violations
        semantic = types.FunctionType(function.__code__, namespace, function.__name__)
        return semantic(rows, {self.trace_path: self.document}, base,
                        terminal_rule_success=self.terminal_rule_success)



def _bounded_semantic_violations(rows, documents, base, *, terminal_rule_success):
    """Check the cycle chain and exact named-rule terminal evidence."""
    try:
        require(len(documents) == 1, "A completed diagnosis must use one exact TRACE.json bundle.")
        document = next(iter(documents.values()))
        require(isinstance(document, dict) and type(document.get("schema_version")) is int
                and document.get("schema_version") == 1, "The trace schema version is unsupported.")
        session = document["session"]["id"]
        require(isinstance(session, str) and session, "The stable logical session identity is absent.")
        completion = document["completion"]
        require(isinstance(completion, dict) and completion.get("trace_complete") is True
                and completion.get("reasons") == [],
                "The trace does not establish complete required observations.")
        coverage = document["coverage"]
        require(isinstance(coverage, dict) and coverage.get("required_complete") is True
                and coverage.get("missing_event_ids", []) == [] and coverage.get("unobserved_regions") == [],
                "The trace does not establish complete traversal coverage.")
        points = document["points"]
        require(isinstance(points, list), "The ordered points array is absent.")
        captures = points + ([document["residual"]] if document.get("residual") is not None else [])
        for point in captures:
            check_capture(point, session)
            require(isinstance(point["hint_log"], dict)
                    and point["hint_log"].get("availability") == "complete", "A point lacks complete hint logs.")
        lookup = {name: (evidence, parse_citations(cites)[0])
                  for _, name, evidence, cites in rows}

        def references(name):
            evidence, citations = lookup[name]
            return evidence, [(pointer_tokens(c.pointer), resolve_citation(c, base, documents))
                              for c in citations]

        def verbatim(name, allowed):
            evidence, refs = references(name)
            values = quoted_values(evidence)
            cited = [value for tokens, value in refs if allowed(tokens) and isinstance(value, str)]
            require(all(value in cited for value in values), f"{name}: quoted text differs from its cited observation.")
            require(cited, f"{name}: cite the exact required observation.")
            return refs

        trigger_refs = verbatim("trigger_goal", lambda t: (len(t) == 3 and t[0] == "points"
                                             or len(t) == 2 and t[0] == "residual")
                 and t[-1] in {"goal", "goal_nonotation"})

        def refusal(name):
            evidence, refs = references(name)
            messages = [(tokens, value) for tokens, value in refs if tokens[-1:] == ["message"]]
            require(len(messages) == 1, f"{name}: cite one exact refusal message.")
            tokens, _ = messages[0]
            observation = refusal_observation(document, "/" + "/".join(tokens))
            record = observation["refusal"]
            require(record["exposure"] == "exposed", f"{name}: the refusing clause is not exposed.")
            values = quoted_values(evidence)
            require(record["message"] in values and record["clause"] in values,
                    f"{name}: quote the exact exposed clause and refusal message.")
            require(all(value in {record["message"], record["clause"]} for value in values),
                    f"{name}: the quoted refusal contains an unsupported value.")
            trial = observation["trial"]
            last = len(trial["commands"]) - 1
            command_tokens = tokens[:-3] + ["hand_call", str(record["hand_call_index"]), "commands", str(last), "command"]
            command, _, before, _ = command_observation(document, command_tokens, session)
            require(command["outcome"] == "refused" and command["refusal"] == record["message"],
                    f"{name}: the final command differs from the recorded refusal.")
            require(command["command"] == trial["command"], f"{name}: the refused command is not the recorded rule.")
            return tokens[:-1], trial, before

        cycles = sorted({int(m[1]) for name in lookup if (m := CYCLE.fullmatch(name))})
        previous, normalization_refs, terminal_snapshot = None, [], None
        diagnosed_rule = final_trial_pointer = None
        for number in cycles:
            prefix = f"cycle.{number}."
            key, initial_trial, state = refusal(prefix + "refusal")
            owner = resolve_pointer(document, "/" + "/".join(key[:2] if key[0] == "points" else key[:1]))
            rule = owner["trigger"].get("rule")
            require(isinstance(rule, str) and rule, "The refusal lacks its diagnosed rule identity.")
            require(diagnosed_rule is None or rule == diagnosed_rule, "A cycle changes the diagnosed rule.")
            diagnosed_rule = rule
            if number == 1:
                for tokens, _ in trigger_refs:
                    length = 2 if tokens[0] == "points" else 1
                    trigger = resolve_pointer(document, "/" + "/".join(tokens[:length]))
                    require(same_state(trigger, state), "The trigger goal differs from the first refusal state.")
            if previous is not None:
                require(key == previous, "A repeated cycle does not start at the preceding next refusal.")
            reason_refs = verbatim(prefix + "reason", lambda t: t[0] in {"points", "residual", "snapshots"}
                                   and any(k in t for k in {"hyps", "evars", "hint_log", "goal", "goal_nonotation", "refusal"}))
            # Reason observations must belong to the current refusal point or its exact before snapshot.
            for tokens, _ in reason_refs:
                if tokens[0] == "snapshots":
                    capture = resolve_pointer(document, "/snapshots/" + tokens[1].replace("~", "~0").replace("/", "~1"))
                else:
                    length = 2 if tokens[0] == "points" else 1
                    capture = resolve_pointer(document, "/" + "/".join(tokens[:length]))
                require(same_state(capture, state), "A reason cites a different proof state.")
            evidence, refs = references(prefix + "normalization")
            values = quoted_values(evidence)
            require(len(refs) == len(values), "Each normalization command needs its own exact citation.")
            for (tokens, value), quoted in zip(refs, values):
                require(tokens[-1] == "command" and quoted == value, "A normalization differs from the observed command.")
                command, _, before, after = command_observation(document, tokens, session)
                require(command["outcome"] == "accepted", "A proposed normalization was refused.")
                require(same_state(state, before), "The normalization chain skips or changes the before state.")
                state = after
                normalization_refs.append(tuple(tokens))
            _, next_refs = references(prefix + "next_refusal")
            if any(tokens[-1:] == ["message"] for tokens, _ in next_refs):
                previous, next_trial, next_state = refusal(prefix + "next_refusal")
            else:
                evidence, _ = references(prefix + "next_refusal")
                require(quoted_values(evidence) == ["accepted"] and len(next_refs) == 1,
                        "Quote and cite the accepted rule command outcome.")
                tokens, value = next_refs[0]
                require(tokens[-1] == "outcome" and value == "accepted", "The next rule command did not succeed.")
                command, next_trial, next_state, terminal_snapshot = command_observation(document, tokens, session)
                final_trial_pointer = "/" + "/".join(tokens[:-3])
                require(command["command"] == next_trial["command"]
                        and next_trial["outcome"] == "accepted"
                        and int(tokens[-2]) == len(next_trial["commands"]) - 1,
                        "The accepted command is not the final recorded rule invocation.")
                previous = None
                require(number == cycles[-1], "A cycle continues after its rule succeeded.")
            require(next_trial["command"] == initial_trial["command"], "The next trial calls a different rule.")
            require(same_state(state, next_state), "The next rule trial does not follow the normalization chain.")
        candidate_tokens = [tuple(tokens) for tokens, _ in references("candidate")[1]]
        require(candidate_tokens == normalization_refs, "The candidate citations differ from the ordered normalization sum.")
        terminal, terminal_refs = references("terminal")
        require(terminal == "success", "A verified refutation certificate is not supported by this route.")
        require(previous is None and terminal_snapshot is not None and final_trial_pointer is not None,
                "The final cycle still records a refusal instead of rule success.")
        terminal_rule_success(document, final_trial_pointer, diagnosed_rule, terminal_refs)
        return []
    except (DiagnosisError, KeyError, IndexError, TypeError, ValueError, AttributeError) as error:
        return [f"Semantic validation: {error}"]

def check(path, *, bundle, expected_map_sha256, expected_request, index_dir,
          references_only=False):
    """Validate complete artifacts before accepting any bounded citation.

    Reference-only mode cannot approve a completed diagnosis or release a repair.
    Full mode retains the cycle rules and requires checked named-rule success.
    """
    path = Path(path)
    errors = legacy.violations(path, structure_only=True)
    if errors:
        return errors
    try:
        with CheckedBundle(bundle, expected_map_sha256=expected_map_sha256,
                           expected_request=expected_request, index_dir=index_dir) as checked:
            rows = legacy.table_rows(path.read_text())
            for _, _, _, text in rows:
                for citation in legacy.parse_citations(text)[0]:
                    require((path.parent / citation.path).resolve() == checked.trace_path,
                            'The diagnosis cites another TRACE bundle.')
                    checked.resolve(citation.pointer)
            if not references_only:
                errors.extend(checked.semantic_violations(rows, path.parent))
    except (OSError, ValueError, KeyError, TypeError, IndexError) as error:
        errors.append('Bounded validation: ' + str(error))
    return errors


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('diagnosis', type=Path)
    parser.add_argument('--bundle', type=Path, required=True)
    parser.add_argument('--map-sha256', required=True)
    parser.add_argument('--request', type=Path, required=True)
    parser.add_argument('--request-sha256', required=True)
    parser.add_argument('--index-dir', type=Path, required=True)
    parser.add_argument('--references-only', action='store_true',
                        help='Check artifact/citation associations without approving completion.')
    args = parser.parse_args(argv)
    if file_sha256(args.request) != args.request_sha256:
        parser.error('The caller request differs from its external binding.')
    errors = check(args.diagnosis, bundle=args.bundle,
        expected_map_sha256=args.map_sha256, expected_request=json.loads(args.request.read_text()),
        index_dir=args.index_dir, references_only=args.references_only)
    for error in errors:
        print(error)
    if errors:
        return 1
    print('Reference-only bounded checks passed.' if args.references_only
          else 'Completed bounded diagnosis checks passed.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
