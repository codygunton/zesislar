import hashlib
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent/'block'))
import coqc_primary
import coqc_certificate
import json
import tempfile
from unittest.mock import patch
import subprocess


class CoqcPrimaryTests(unittest.TestCase):
    def rendered(self):
        statement = 'Lemma Boundary : selectedCode -∗ instr_body 0x10 actualEntry.'
        return {'source': statement+'\nProof.\ntry zesu_block.\nQed.\nPrint Assumptions Boundary.\n',
                'lemma': 'Boundary', 'entry_pc': '0x10', 'entry_definition': 'Contracts.actualEntry',
                'scope': 'unproved native designed boundary',
                'statement_sha256': hashlib.sha256(statement.encode()).hexdigest()}

    def test_recorder_preserves_statement_and_requests_exact_primary_budget(self):
        rendered = self.rendered()
        source = coqc_primary.instrument(rendered)
        statement = source[source.index('Lemma Boundary'):source.index('\nProof.\n')]
        self.assertEqual(hashlib.sha256(statement.encode()).hexdigest(), rendered['statement_sha256'])
        self.assertEqual(source.count('Timeout 300 try zesu_block.'), 1)
        self.assertIn('Show Existentials.\nQed.', source)
        self.assertNotIn('Unshelve.', source)
        self.assertNotIn('Abort.', source)

    def test_non_native_or_changed_statement_is_rejected(self):
        for update in ({'scope': 'capture entailment only'}, {'entry_pc': '0x20'},
                       {'statement_sha256': '0'*64}, {'entry_definition': None}):
            with self.assertRaisesRegex(ValueError, 'signature is unavailable'):
                coqc_primary.instrument({**self.rendered(), **update})

    def test_changed_primary_and_excess_budget_are_rejected(self):
        rendered = self.rendered()
        rendered['source'] = rendered['source'].replace('try zesu_block.', 'exact I.')
        with self.assertRaisesRegex(ValueError, 'unchanged tactic'):
            coqc_primary.instrument(rendered)
        with self.assertRaisesRegex(ValueError, 'budget'):
            coqc_primary.instrument(self.rendered(), 301)

    def test_missing_or_nonempty_assumption_certificate_cannot_verify(self):
        self.assertFalse(coqc_primary.assumptions_result('', 'Boundary')['verified'])
        self.assertFalse(coqc_primary.assumptions_result('Axioms:\nunsound : False', 'Boundary')['verified'])
        self.assertFalse(coqc_primary.assumptions_result('Closed under the global context\nAxioms:', 'Boundary')['verified'])
        self.assertEqual(coqc_primary.assumptions_result('Closed under the global context', 'Boundary')['assumptions'], [])

    def test_existing_recorder_is_reused_without_redefinition(self):
        rendered = self.rendered()
        rendered['source'] = coqc_primary.chain_goals.RECORDER + rendered['source']
        instrumented = coqc_primary.instrument(rendered)
        self.assertEqual(instrumented.count('Ltac chain_print_environment '), 1)
        self.assertEqual(instrumented.count('Ltac chain_print_goal '), 1)

    def test_complete_fields_recover_missing_final_end_markers(self):
        first = 'CHAIN-GOAL-BEGIN "active"\nCHAIN-GOAL-ENV coq CHAIN-FIELD-END\nCHAIN-GOAL-CONCLUSION True CHAIN-FIELD-END\n'
        second = first.replace('True', 'False') + 'CHAIN-GOAL-END\n'
        self.assertEqual([g['conclusion'] for g in coqc_primary.decode_active(first+second)], ['True', 'False'])
        with self.assertRaisesRegex(ValueError, 'terminated conclusion'):
            coqc_primary.decode_active(first.replace('True CHAIN-FIELD-END', 'True'))

    def test_diagnostic_local_definitions_keep_their_bodies_without_weakening_default_parser(self):
        output = ('CHAIN-GOAL-BEGIN active\n'
            'CHAIN-GOAL-LOCAL LET : nat CHAIN-FIELD-END\n'
            'CHAIN-GOAL-SORT LET : Set CHAIN-FIELD-END\n'
            'CHAIN-GOAL-VALUE LET : 3 + 4 CHAIN-FIELD-END\n'
            'CHAIN-GOAL-ENV coq CHAIN-FIELD-END\n'
            'CHAIN-GOAL-CONCLUSION LET = 7 CHAIN-FIELD-END\nCHAIN-GOAL-END\n')
        with self.assertRaisesRegex(ValueError, 'unresolved native local definitions'):
            coqc_primary.chain_goals.parse_goals(output)
        goals = coqc_primary.decode_active(output)
        self.assertEqual(goals[0]['local_values'], {'LET': '3 + 4'})
        self.assertIn('LET := 3 + 4 : nat', goals[0]['context'])

    def test_missing_primary_or_recorder_keeps_active_group_unavailable(self):
        self.assertIsNone(coqc_primary.diagnostic_active('Error: inconsistent assumptions'))
        self.assertIsNone(coqc_primary.diagnostic_active('COQC-PRIMARY-BEGIN\nproof limit exceeded: time'))
        self.assertEqual(coqc_primary.diagnostic_active(
            'COQC-PRIMARY-BEGIN\nChars 1 - 2 [Show~Existentials.] 0.01 secs'), [])

    def test_native_certificate_requires_kernel_artifact_and_no_inherited_debts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            rendered = {**self.rendered(), 'successors': ['0x20']}
            source, log, artifact = root/'proof.v', root/'log', root/'proof.vo'
            source.write_text(coqc_primary.instrument(rendered))
            log.write_text('Closed under the global context')
            artifact.write_bytes(b'test artifact')
            evidence = {'compiler': {'exit_code': 0, 'limit': None,
                'compiled_object': {'path': str(artifact), 'sha256': coqc_primary.digest(artifact)}},
                'native_qed_compiled': True, 'inherited_debts': {}, 'primary_tactic_entered': True,
                'primary_tactic': 'try zesu_block.', 'primary_timeout': 300,
                'original_source_sha256': hashlib.sha256(rendered['source'].encode()).hexdigest(),
                'statement_sha256': rendered['statement_sha256'],
                'entry_pc': rendered['entry_pc'], 'entry_definition': rendered['entry_definition'], 'successors': rendered['successors'],
                'source': str(source), 'source_sha256': coqc_primary.digest(source),
                'log': str(log), 'log_sha256': coqc_primary.digest(log),
                'assumption_verification': {'verified': True, 'assumptions': []}}
            self.assertTrue(coqc_certificate.native_closed(evidence, rendered))
            for update in ({'inherited_debts': {'shelf': ['debt']}}, {'primary_timeout': 299},
                           {'native_qed_compiled': False}, {'entry_pc': '0x800d698c'}, {'successors': ['0x30']},
                           {'assumption_verification': {'verified': True, 'assumptions': ['axiom']}}):
                self.assertFalse(coqc_certificate.native_closed({**evidence, **update}, rendered))
            artifact.write_bytes(b'changed object')
            self.assertFalse(coqc_certificate.native_closed(evidence, rendered))


class CompletionBudgetTests(unittest.TestCase):
    rendered = CoqcPrimaryTests.rendered
    def test_cpu_instrumentation_preserves_tactic_without_wall_timeout(self):
        source = coqc_primary.instrument(self.rendered(), cpu_seconds=1200)
        self.assertNotIn('Timeout ', source)
        self.assertIn('\ntry zesu_block.\n', source)
        self.assertIn('Show Existentials.\nQed.', source)
        for invalid in (0, 1201, -1, 1.5):
            with self.assertRaisesRegex(ValueError, 'CPU budget'):
                coqc_primary.instrument(self.rendered(), cpu_seconds=invalid)

    def test_completion_compile_sets_both_monitors_and_cpu_guard(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root/'Profile.v'
            source.write_text('Set Ltac Profiling.\n')
            policy = coqc_primary.budget_policy(cpu_seconds=1200)
            with patch.object(coqc_primary.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, '', '')) as run:
                coqc_primary.compile_source(source, root/'out', root/'build', policy=policy)
            environment = run.call_args.kwargs['env']
            self.assertEqual(environment['ZESU_PRIMARY_CPU_LIMIT'], '1200')
            self.assertEqual(environment['ZESU_PROOF_CPU_LIMIT'], '1200')
            self.assertEqual(environment['ZESU_PRIMARY_WALL_LIMIT'], 'none')
            self.assertEqual(environment['ZESU_SCRATCH_WALL_SECONDS'], 'none')
            self.assertEqual(source.read_text(), 'Set Ltac Profiling.\n')

    def test_certificate_cpu_policy_requires_matching_compiler_limits(self):
        policy = coqc_primary.budget_policy(cpu_seconds=1200)
        evidence = {'proof_budget': policy, 'primary_timeout': None}
        compiler = {'limits': {'cpu_seconds': 1200, 'module_seconds': None, 'rss_kib': 6291456}}
        self.assertTrue(coqc_certificate.valid_budget(evidence, compiler))
        for field, value in (('cpu_seconds', 300), ('module_seconds', 300), ('rss_kib', 0)):
            changed = {'limits': {**compiler['limits'], field: value}}
            self.assertFalse(coqc_certificate.valid_budget(evidence, changed))

    def test_default_budget_remains_historical_wall_policy(self):
        self.assertEqual(coqc_primary.budget_policy(), {'kind': 'wall', 'cpu_seconds': None,
            'wall_seconds': 300, 'memory_kib': 6291456})
        self.assertEqual(coqc_primary.completion_environment(coqc_primary.budget_policy())['ZESU_SCRATCH_WALL_SECONDS'], '300')

    def test_postcompiler_report_records_the_actual_scratch_command(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            rendered = {**self.rendered(), 'successors': ['0x20']}
            command = ['scratch.sh', str(root/'out/Boundary.v'), str(root/'build')]
            output = 'COQC-PRIMARY-BEGIN\nAttempt to save an incomplete proof\n'
            log = root/'compiler.log'
            log.write_text(output)
            done = subprocess.CompletedProcess(command, 1, output, '')
            compiler = {'exit_code': 1, 'limit': None, 'compiled_object': None}
            with patch.object(coqc_primary, 'compile_source', return_value=(done, output, log, compiler, 0.25)):
                result = coqc_primary.run_primary(rendered, root/'out', root/'build',
                    inherited_debts={'pending_goals': [], 'shelved_goals': []}, cpu_seconds=1200)
            self.assertEqual(result['scratch_command'], command)
            retained = json.loads((root/'out/evidence.json').read_text())
            self.assertEqual(retained['scratch_command'], command)
            self.assertEqual(retained['proof_budget']['cpu_seconds'], 1200)
            self.assertEqual(retained['outcome'], 'native-residual')
            self.assertFalse(retained['block_closed'])

    def test_cpu_stop_with_interrupted_capture_retains_limit_classification(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            rendered = {**self.rendered(), 'successors': ['0x20']}
            command = ['scratch.sh', str(root/'out/Boundary.v'), str(root/'build')]
            output = ('COQC-PRIMARY-BEGIN\nCHAIN-GOAL-BEGIN active\n'
                      'CHAIN-GOAL-ENV coq CHAIN-FIELD-END\n'
                      'CHAIN-GOAL-CONCLUSION interrupted')
            log = root/'compiler.log'
            log.write_text(output)
            done = subprocess.CompletedProcess(command, -9, output, '')
            compiler = {'exit_code': -9, 'limit': 'cpu', 'compiled_object': None,
                        'cpu_seconds': 1199.857448, 'peak_rss_kib': 3678200}
            with patch.object(coqc_primary, 'compile_source',
                              return_value=(done, output, log, compiler, 1204.841451)):
                result = coqc_primary.run_primary(rendered, root/'out', root/'build',
                    inherited_debts={'pending_goals': [], 'shelved_goals': []}, cpu_seconds=1200)
            retained = json.loads((root/'out/evidence.json').read_text())
            self.assertEqual(result['outcome'], 'limit-stop')
            self.assertEqual(retained['outcome'], 'limit-stop')
            self.assertEqual(retained['compiler'], compiler)
            self.assertEqual(retained['proof_budget']['cpu_seconds'], 1200)
            self.assertIsNone(retained['primary_timeout'])
            self.assertIsNone(retained['active_goals'])
            self.assertTrue(retained['capture_error'])
            self.assertFalse(retained['block_closed'])
            self.assertEqual(log.read_text(), output)

    def test_completion_exceptions_require_the_authorized_entry(self):
        for pc in ('0x800d6a24', '0x800d6ac4'):
            policy = coqc_primary.budget_policy(cpu_seconds=2400, entry_pc=pc)
            self.assertEqual(policy['cpu_seconds'], 2400)
            self.assertEqual(policy['completion_entry'], pc)
            self.assertEqual(policy['optimization_debt'], 'issue#10')
        memory = coqc_primary.budget_policy(cpu_seconds=1200, memory_gib=12, entry_pc='0x800d698c')
        environment = coqc_primary.completion_environment(memory)
        self.assertEqual(environment['ZESU_PRIMARY_MEMORY_GIB'], '12')
        self.assertEqual(environment['ZESU_SCRATCH_MEMORY_GIB'], '12')
        for values in ({'cpu_seconds': 2400}, {'cpu_seconds': 2400, 'entry_pc': '0x800d6974'},
                       {'cpu_seconds': 2401, 'entry_pc': '0x800d6a24'},
                       {'cpu_seconds': 1200, 'memory_gib': 12},
                       {'cpu_seconds': 2400, 'memory_gib': 12, 'entry_pc': '0x800d6a24'}):
            with self.assertRaises(ValueError):
                coqc_primary.budget_policy(**values)

    def test_certificate_rejects_exception_transferred_to_another_entry(self):
        policy = coqc_primary.budget_policy(cpu_seconds=2400, entry_pc='0x800d6a24')
        evidence = {'entry_pc': '0x800d6a24', 'proof_budget': policy, 'primary_timeout': None}
        compiler = {'limits': {'cpu_seconds': 2400, 'module_seconds': None, 'rss_kib': 6291456}}
        self.assertTrue(coqc_certificate.valid_budget(evidence, compiler))
        self.assertFalse(coqc_certificate.valid_budget({**evidence, 'entry_pc': '0x800d6974'}, compiler))
        memory = coqc_primary.budget_policy(cpu_seconds=1200, memory_gib=12, entry_pc='0x800d698c')
        compiler['limits'].update(cpu_seconds=1200, rss_kib=12582912)
        self.assertTrue(coqc_certificate.valid_budget({'entry_pc': '0x800d698c', 'proof_budget': memory, 'primary_timeout': None}, compiler))
        self.assertFalse(coqc_certificate.valid_budget({'entry_pc': '0x800d6a24', 'proof_budget': memory, 'primary_timeout': None}, compiler))


class DiagnosticProbeBudgetTests(unittest.TestCase):
    rendered = CoqcPrimaryTests.rendered

    def test_explicit_probe_policy_preserves_native_tactic(self):
        policy = coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True)
        self.assertEqual(policy, {'kind': 'probe', 'cpu_seconds': None,
            'wall_seconds': None, 'memory_kib': 64*1024*1024,
            'optimization_debt': 'issue#10'})
        source = coqc_primary.instrument(self.rendered(), memory_gib=64, diagnostic_probe=True)
        self.assertNotIn('Timeout ', source)
        self.assertIn('\ntry zesu_block.\n', source)
        for values in ({'memory_gib': 6}, {'memory_gib': 64, 'cpu_seconds': 14400}):
            with self.assertRaises(ValueError):
                coqc_primary.budget_policy(diagnostic_probe=True, **values)
        with self.assertRaises(ValueError):
            coqc_primary.budget_policy(memory_gib=64, cpu_seconds=1200)

    def test_probe_environment_does_not_contaminate_default_policy(self):
        environment = coqc_primary.completion_environment(
            coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True))
        self.assertEqual(environment['ZESU_PRIMARY_CPU_LIMIT'], 'none')
        self.assertEqual(environment['ZESU_PROOF_CPU_LIMIT'], 'unlimited')
        self.assertEqual(environment['ZESU_MODULE_LIMIT_GIB'], '64')
        self.assertEqual(environment['ZESU_SCRATCH_WALL_SECONDS'], 'none')
        default = coqc_primary.completion_environment(coqc_primary.budget_policy())
        self.assertEqual(default['ZESU_DIAGNOSTIC_PROBE'], '0')
        self.assertEqual(default['ZESU_PRIMARY_MEMORY_GIB'], '6')

    def test_certificate_requires_measured_child_and_scope_limits(self):
        policy = coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True)
        evidence = {'proof_budget': policy, 'primary_timeout': None}
        compiler = {'limits': {'cpu_seconds': None, 'module_seconds': None,
            'rss_kib': 64*1024*1024}, 'actual_cpu_limits': {'soft': None, 'hard': None},
            'actual_scope_limits': {'memory_max_bytes': 64*1024**3, 'memory_swap_max_bytes': 0}}
        self.assertTrue(coqc_certificate.valid_budget(evidence, compiler))
        for key, value in [('actual_cpu_limits', None),
                ('actual_cpu_limits', {'soft': 1200, 'hard': 1200}),
                ('actual_scope_limits', None),
                ('actual_scope_limits', {'memory_max_bytes': 6*1024**3, 'memory_swap_max_bytes': 0})]:
            self.assertFalse(coqc_certificate.valid_budget(evidence, {**compiler, key: value}))
        self.assertFalse(coqc_certificate.valid_budget(
            {**evidence, 'proof_budget': {**policy, 'optimization_debt': None}}, compiler))

    def test_wrong_probe_scope_prevents_compiler_spawn(self):
        environment = coqc_primary.completion_environment(
            coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True))
        with patch.dict(coqc_primary.os.environ, {**environment,
                'ZESU_PRIMARY_COMPILER_RECORD': '/unused'}, clear=True), \
                patch.object(coqc_primary, 'probe_scope_limits', return_value={
                    'memory_max_bytes': 6*1024**3, 'memory_swap_max_bytes': 0}), \
                patch.object(coqc_primary.subprocess, 'Popen') as spawn:
            with self.assertRaisesRegex(ValueError, 'scope limits'):
                coqc_primary.compiler_run([])
            spawn.assert_not_called()

    def test_scratch_policy_accepts_only_explicit_unlimited_probe(self):
        import os
        source = (Path(__file__).parent/'coqc_scratch.sh').read_text()
        policy_code = source.split("<<'PY'\n", 1)[1].split('source = Path(sys.argv[1])', 1)[0]
        environment = coqc_primary.completion_environment(
            coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True))
        with patch.dict(os.environ, environment, clear=True):
            scope = {}
            exec(policy_code, scope)
            self.assertIsNone(scope['wall_limit'])
            self.assertEqual(scope['memory_gib'], 64)
        for change in [{'ZESU_IN_GATE': '1'}, {'ZESU_PRIMARY_CPU_LIMIT': '14400'},
                {'ZESU_PROBE_ISSUE': ''}, {'ZESU_SCRATCH_MEMORY_GIB': '6'},
                {'ZESU_SCRATCH_WALL_SECONDS': '300'}]:
            with patch.dict(os.environ, {**environment, **change}, clear=True):
                with self.assertRaises(SystemExit):
                    exec(policy_code, {})

    def test_child_limit_read_failure_stops_and_records_owned_child(self):
        environment = coqc_primary.completion_environment(
            coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True))
        with tempfile.TemporaryDirectory() as directory:
            record = Path(directory)/'compiler.json'
            environment.update(ZESU_PRIMARY_COMPILER_RECORD=str(record),
                               ZESU_PRIMARY_COMPILED_OBJECT=str(Path(directory)/'unused.vo'))
            from unittest.mock import MagicMock
            child = MagicMock()
            child.pid = 123
            child.poll.side_effect = [None]
            child.wait.return_value = -15
            scope = {'memory_max_bytes': 64*1024**3, 'memory_swap_max_bytes': 0}
            with patch.dict(coqc_primary.os.environ, environment, clear=True), \
                    patch.object(coqc_primary, 'probe_scope_limits', side_effect=[scope, ValueError('bad cgroup')]), \
                    patch.object(coqc_primary.resource, 'prlimit', return_value=(-1, -1)), \
                    patch.object(coqc_primary, 'probe_memory_events', return_value={'oom_kill': 0}), \
                    patch.object(coqc_primary.subprocess, 'Popen', return_value=child):
                self.assertEqual(coqc_primary.compiler_run([]), 1)
            child.terminate.assert_called_once()
            retained = json.loads(record.read_text())
            self.assertEqual(retained['limit'], 'policy')
            self.assertEqual(retained['policy_error'], 'bad cgroup')
            self.assertEqual(retained['exit_code'], -15)

    def test_probe_records_scope_oom_stop_without_cpu_limit(self):
        environment = coqc_primary.completion_environment(
            coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True))
        with tempfile.TemporaryDirectory() as directory:
            record = Path(directory)/'compiler.json'
            environment.update(ZESU_PRIMARY_COMPILER_RECORD=str(record))
            from unittest.mock import MagicMock
            child = MagicMock()
            child.pid = 123
            child.poll.return_value = -9
            child.wait.return_value = -9
            scope = {'memory_max_bytes': 64*1024**3, 'memory_swap_max_bytes': 0}
            with patch.dict(coqc_primary.os.environ, environment, clear=True), \
                    patch.object(coqc_primary, 'probe_scope_limits', return_value=scope), \
                    patch.object(coqc_primary, 'probe_memory_events', side_effect=[{'oom_kill': 0}, {'oom_kill': 1}]), \
                    patch.object(coqc_primary.subprocess, 'Popen', return_value=child):
                self.assertEqual(coqc_primary.compiler_run([]), 1)
            retained = json.loads(record.read_text())
            self.assertEqual(retained['limit'], 'memory')
            self.assertIsNone(retained['limits']['cpu_seconds'])
            self.assertEqual(retained['scope_memory_events_after']['oom_kill'], 1)
            self.assertIsNone(retained['actual_cpu_limits'])
            self.assertFalse(coqc_certificate.valid_budget(
                {'proof_budget': coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True),
                 'primary_timeout': None}, retained))

    def test_exit_telemetry_failure_preserves_valid_limits_and_compiler_exit(self):
        from types import SimpleNamespace
        from unittest.mock import MagicMock
        environment = coqc_primary.completion_environment(
            coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True))
        scope = {'memory_max_bytes': 64*1024**3, 'memory_swap_max_bytes': 0}
        original_read = Path.read_text
        for failure in ('missing_rss', 'missing_status', 'missing_stat'):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as directory:
                record = Path(directory)/'compiler.json'
                child = MagicMock()
                child.pid = 123
                child.poll.side_effect = [None, 1]
                child.wait.return_value = 1
                def read(path, *args, **kwargs):
                    if str(path) == '/proc/123/status':
                        if failure == 'missing_rss':
                            return 'State:\tZ (zombie)\n'
                        if failure == 'missing_status':
                            raise FileNotFoundError()
                        return 'VmRSS:\t100 kB\n'
                    if str(path) == '/proc/123/stat':
                        raise ProcessLookupError()
                    return original_read(path, *args, **kwargs)
                usage = [SimpleNamespace(ru_utime=0, ru_stime=0, ru_maxrss=0),
                         SimpleNamespace(ru_utime=1, ru_stime=.25, ru_maxrss=1234),
                         SimpleNamespace(ru_utime=1, ru_stime=.25, ru_maxrss=1234)]
                with patch.dict(coqc_primary.os.environ, {**environment,
                        'ZESU_PRIMARY_COMPILER_RECORD': str(record)}, clear=True), \
                        patch.object(coqc_primary, 'probe_scope_limits', return_value=scope), \
                        patch.object(coqc_primary.resource, 'prlimit', return_value=(-1, -1)), \
                        patch.object(coqc_primary.resource, 'getrusage', side_effect=usage), \
                        patch.object(coqc_primary, 'probe_memory_events', return_value={'oom_kill': 0}), \
                        patch.object(coqc_primary.subprocess, 'Popen', return_value=child), \
                        patch.object(coqc_primary.time, 'sleep'), \
                        patch.object(Path, 'read_text', read):
                    self.assertEqual(coqc_primary.compiler_run([]), 1)
                child.terminate.assert_not_called()
                child.kill.assert_not_called()
                retained = json.loads(record.read_text())
                self.assertEqual(retained['exit_code'], 1)
                self.assertIsNone(retained['limit'])
                self.assertIsNone(retained['policy_error'])
                self.assertEqual(retained['telemetry_errors']['count'], 1)
                self.assertEqual(retained['actual_cpu_limits'], {'soft': None, 'hard': None})
                self.assertEqual(retained['actual_scope_limits'], scope)
                self.assertEqual(retained['cpu_seconds'], 1.25)
                self.assertEqual(retained['peak_rss_kib'], 1234)

    def test_missing_actual_limit_query_still_stops_owned_child(self):
        from unittest.mock import MagicMock
        environment = coqc_primary.completion_environment(
            coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True))
        with tempfile.TemporaryDirectory() as directory:
            record = Path(directory)/'compiler.json'
            child = MagicMock()
            child.pid = 123
            child.poll.return_value = None
            child.wait.return_value = -15
            scope = {'memory_max_bytes': 64*1024**3, 'memory_swap_max_bytes': 0}
            with patch.dict(coqc_primary.os.environ, {**environment,
                    'ZESU_PRIMARY_COMPILER_RECORD': str(record)}, clear=True), \
                    patch.object(coqc_primary, 'probe_scope_limits', return_value=scope), \
                    patch.object(coqc_primary.resource, 'prlimit', side_effect=ProcessLookupError()), \
                    patch.object(coqc_primary, 'probe_memory_events', return_value={'oom_kill': 0}), \
                    patch.object(coqc_primary.subprocess, 'Popen', return_value=child):
                self.assertEqual(coqc_primary.compiler_run([]), 1)
            child.terminate.assert_called_once()
            retained = json.loads(record.read_text())
            self.assertEqual(retained['limit'], 'policy')
            self.assertEqual(retained['policy_error'], 'The live diagnostic child limits are unavailable')
            self.assertIsNone(retained['actual_cpu_limits'])

    def test_changed_child_limits_still_stop_owned_child(self):
        from unittest.mock import MagicMock
        environment = coqc_primary.completion_environment(
            coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True))
        scope = {'memory_max_bytes': 64*1024**3, 'memory_swap_max_bytes': 0}
        for cpu, child_scope in [((1200, 1200), scope),
                ((-1, -1), {**scope, 'memory_max_bytes': 6*1024**3})]:
            with self.subTest(cpu=cpu, scope=child_scope), tempfile.TemporaryDirectory() as directory:
                record = Path(directory)/'compiler.json'
                child = MagicMock()
                child.pid = 123
                child.poll.return_value = None
                child.wait.return_value = -15
                with patch.dict(coqc_primary.os.environ, {**environment,
                        'ZESU_PRIMARY_COMPILER_RECORD': str(record)}, clear=True), \
                        patch.object(coqc_primary, 'probe_scope_limits', side_effect=[scope, child_scope]), \
                        patch.object(coqc_primary.resource, 'prlimit', return_value=cpu), \
                        patch.object(coqc_primary, 'probe_memory_events', return_value={'oom_kill': 0}), \
                        patch.object(coqc_primary.subprocess, 'Popen', return_value=child):
                    self.assertEqual(coqc_primary.compiler_run([]), 1)
                child.terminate.assert_called_once()
                retained = json.loads(record.read_text())
                self.assertEqual(retained['limit'], 'policy')
                self.assertEqual(retained['policy_error'], 'The diagnostic child limits differ from the probe policy')
