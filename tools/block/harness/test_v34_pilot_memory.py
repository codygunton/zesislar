"""Check the public v3.4 booking rule with private completed measurements."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from test_effective_overrides_authority import EffectiveOverridesAuthority, binding
import memory_policy as P
import port_native_policy
from scratch_imports import install_rules_import
from scratch_statement import source_statement


class V34PilotMemory(unittest.TestCase):
    def save(self, path, data):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data))
        return binding(path)

    def setUp(self):
        EffectiveOverridesAuthority.setUp(self)
        original = json.loads(Path(P.PORT_V34_TARGETS['path']).read_text())
        self.rows = []
        self.targets = []
        self.jobs = []
        self.staged = {}
        rules = self.root / 'NATIVE-RULES.v'
        rules.write_text('Require Export ZesuSsz.Automation.Sets.V34Candidates.\n')
        self.rules = binding(rules)
        self.policy = self.save(self.root / 'NATIVE-POLICY.json', {
            'hook_enabled': False, 'database': 'zesu_entry_normalize', 'registrations': [self.rules]})
        self.enterContext(patch.object(P, 'PORT_V34_POLICY_SHA256', self.policy['sha256']))
        inventory = []
        for index, target in enumerate(original['rows']):
            case = next(row for row in self.authorities[23]['cases'] if row['block'] == target['key'])
            job = EffectiveOverridesAuthority.job(self, case)
            self.jobs.append(job)
            directory = self.root / case['block']
            directory.mkdir()
            old = directory / 'Original.v'
            old.write_bytes(Path(case['source']['path']).read_bytes().replace(
                b'Require Import ZesuSsz.Automation.EffectiveOverrides.\n', b'', 1))
            native = directory / 'Native.v'
            native.write_bytes(Path(case['source']['path']).read_bytes())
            before = source_statement(native)
            installed = install_rules_import(native, 'ZesuSsz.Evidence.RuleScratchRules', source_statement)
            self.assertEqual(installed['placement'], 'after_existing_imports')
            self.assertEqual(source_statement(native)['statement'], before['statement'])
            self.assertEqual(source_statement(native)['native_body'], 'zesu_block.')
            self.staged[case['block']] = binding(native)
            job['target']['source_sha256'] = binding(native)['sha256']
            inventory.append(dict(key=case['block'], module=case['module'], pc=case['pc'],
                source_sha256=binding(old)['sha256'], statement_sha256=case['statement_sha256']))
            if case['block'] == '800d6974':
                continue
            peak = 100 if index == 0 else 3 * P.GIB + index
            state = {'goals': [], 'stack': [], 'shelf': [], 'given_up': []}
            state['kernel_groups'] = deepcopy(state)
            state_binding = self.save(directory / 'STATE.json', state)
            state_binding['state_source'] = 'successful_command_returned_state'
            accounting = {'aggregate_peak_bytes': peak, 'final_memory_accounting_available': True,
                          'scope': 'Private completed aggregate fixture.',
                          'memory_events': {'counters': {}}}
            result = dict(module=case['module'], statement_sha256=case['statement_sha256'],
                status='native_open', normal_tactic_return=True, final_memory_accounting_available=True,
                CPU=accounting, aggregate_peak_bytes=peak, complete_state=state_binding,
                group_counts={'active': 0, 'focus_frames': 0, 'frame_goals': 0, 'shelves': 0, 'given_up': 0})
            if case['block'] in {'800d6a14', '800d6ab4'}:
                result['status'] = 'unresolved'
                result.pop('normal_tactic_return')
                result['complete_state']['state_source'] = 'reported_last_valid_state'
            self.rows.append(dict(format='completed_stock_v34_pilot_v1', route='stock_zesu_block',
                block=case['block'], module=case['module'], native_source=binding(native),
                original_source=binding(old), statement_sha256=case['statement_sha256'],
                result=self.save(directory / 'RESULT.json', result),
                accounting=self.save(directory / 'CPU-FINAL.json', accounting),
                closure=self.save(directory / 'CLOSURE.json', {'all_owned_actors_closed': True}),
                release=self.save(directory / 'RELEASE.json', {'released': True, 'bytes': 8 * P.GIB}),
                targets={}, authority=self.profiles[23]['authority'],
                native_rules=self.rules, normalization_policy=self.policy))
            self.targets.append(job['target'])
        target_binding = self.save(self.root / 'TARGETS.json', {'rows': inventory})
        self.enterContext(patch.object(P, 'PORT_V34_TARGETS', target_binding))
        for row in self.rows:
            row['targets'] = target_binding
        completed = self.save(self.root / 'COMPLETED.json', {
            'schema': 'port.v34.completed-peak-authority.v1', 'targets_sha256': target_binding['sha256'],
            'rows': [dict(block=row['block'], module=row['module'], statement_sha256=row['statement_sha256'],
                         peak_bytes=P.read(row['accounting'])['aggregate_peak_bytes'],
                         provenance_version='v3.1' if row['block'] in {'800d6a14', '800d6ab4'} else 'v3.2',
                         receipt_sha256={key: row[key]['sha256'] for key in ['result', 'accounting', 'closure', 'release']})
                     for row in self.rows]})
        self.enterContext(patch.object(P, 'PORT_V34_COMPLETED', completed))
        for row in self.rows:
            row['completed_authority'] = completed
        self.bank_files = {}
        self.old_bank = {}
        self.new_bank = {}
        self.retained_bank = {}
        for module in ['ZesuSsz.Generated.DecodeItem.MachinePilot180Entries',
                       'ZesuSsz.Generated.DecodeItem.MachinePilot180Structural',
                       'ZesuSsz.Contracts.RlpDecodeItemContract']:
            self.bank_files[module] = {}
            for variant, hashes in [('OLD', self.old_bank), ('NEW', self.new_bank), ('RETENTION', self.retained_bank)]:
                path = self.root / (variant + '-' + module.split('.')[-1] + '.v')
                path.write_text('Definition fixture_' + variant + ' := 0.\n')
                self.bank_files[module][variant] = path
                hashes[module] = binding(path)['sha256']
        self.banks = self.save(self.root / 'BANKS.json', {
            'OLD_sources': self.old_bank, 'NEW6a00_sources': self.new_bank,
            'retention_sources': {k: v for k, v in self.retained_bank.items() if '.Generated.' in k},
            'retention_cases': ['800d6aa8', '800d6ab4'],
            'case_modules': {key: list(self.old_bank) for key in [job['key'] for job in self.jobs] + ['NEW:800d6a00']},
            'shared_overlay': self.save(self.root / 'SHARED-SOURCES.json', [])})
        self.enterContext(patch.object(P, 'PORT_V34_BANKS', self.banks))
        case = next(case for case in self.authorities[23]['cases'] if case['block'] == '800d6a00')
        comparison = self.save(self.root / 'NEW6A00.json', {
            'schema': 'port.v34.new-comparison-authority.v1', 'variant': 'NEW6a00', 'block': case['block'],
            'module': case['module'], 'pc': case['pc'], 'statement_sha256': case['statement_sha256'],
            'caller': case['source'], 'banks': self.banks,
            'claim_bytes': P.PORT_FENCE, 'physical_fence_bytes': P.PORT_FENCE})
        self.enterContext(patch.object(P, 'PORT_V34_NEW', comparison))
        self.comparison = comparison
        self.profile = dict(self.profiles[23], memory_booking=P.PORT_V34_PEAK_BOOKING,
                            pilot_targets=target_binding, native_rules=self.rules, normalization_policy=self.policy,
                            completed_peak_authority=completed, bank_authority=self.banks)
        self.profile_binding = self.save(self.root / 'PROFILE.json', self.profile)

    def context(self, job, variant=None):
        case = next(row for row in self.authorities[23]['cases'] if row['block'] == job['key'])
        sources = [dict(self.staged[case['block']], module=case['module']),
                   dict(self.rules, module='ZesuSsz.Evidence.RuleScratchRules')] + self.authorities[23]['production_sources']
        for module, variants in self.bank_files.items():
            selected = variant or ('RETENTION' if job['key'] in {'800d6aa8', '800d6ab4'} and '.Generated.' in module else 'OLD')
            sources.append(dict(binding(variants[selected]), module=module))
        config = {'prepared_workspace': '/', 'declarations_only': False, 'prerequisite_modules': [],
                  'proof_runtime': {'module_files': {row['module']: row['path'] for row in sources}}}
        return config

    def workload(self, job):
        return P.workload_for_job(self.profile_binding, job, self.context(job))

    def checked(self, index=0):
        return P.completed(self.rows[index], self.targets[index])

    def test_exact_fifteen_formula_values_and_one_gib_floor(self):
        for row, target in zip(self.rows, self.targets):
            checked, reason = P.completed(row, target)
            self.assertIsNone(reason)
            peak = P.read(row['accounting'])['aggregate_peak_bytes']
            self.assertEqual(checked['claim_bytes'], max(P.GIB, (3 * peak + 1) // 2))
            self.assertEqual(checked['memory_metric'], 'aggregate_memory.peak')

    def test_public_workload_keeps_32_gib_fence_and_no_cpu_stops(self):
        for job in self.jobs:
            sized = P.apply_job(job, self.rows, self.workload(job))
            self.assertEqual(P.validate_job(sized), sized['claim_bytes'])
            self.assertEqual(sized['physical_fence_bytes'], 32 * P.GIB)
            self.assertEqual(port_native_policy.cpu_budgets(sized), (None, None))
            if job['key'] == '800d6974':
                self.assertEqual(sized['claim_bytes'], 32 * P.GIB)

    def test_missing_measurement_refuses_instead_of_defaulting(self):
        job = self.jobs[0]
        with self.assertRaisesRegex(ValueError, 'exact completed v3.2 measurement'):
            P.apply_job(job, [], self.workload(job))

    def test_wrong_block_and_unauthorized_target_refuse(self):
        wrong = deepcopy(self.rows[0])
        wrong['block'] = '800d697c'
        with self.assertRaisesRegex(ValueError, 'public inventory'):
            P.completed(wrong, self.targets[0])
        for field in ['module', 'pc', 'statement_sha256']:
            target = dict(self.targets[0], **{field: 'wrong'})
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'public inventory'):
                P.completed(self.rows[0], target)

    def test_changed_receipt_refuses(self):
        for name in ['result', 'accounting', 'closure', 'release']:
            path = Path(self.rows[0][name]['path'])
            before = path.read_bytes()
            path.write_bytes(before + b' ')
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'binding changed'):
                self.checked()
            path.write_bytes(before)

    def test_rehashed_changed_receipt_cannot_replace_approved_measurement(self):
        row = deepcopy(self.rows[0])
        result = P.read(row['result'])
        result['aggregate_peak_bytes'] += 1
        row['result'] = self.save(self.root / 'REHASHED-RESULT.json', result)
        checked, reason = P.completed(row, self.targets[0])
        self.assertIsNone(checked)
        self.assertIn('not authorized', reason)

    def test_missing_incomplete_or_mismatched_peak_refuses(self):
        row = self.rows[0]
        for field, value in [('aggregate_peak_bytes', None), ('final_memory_accounting_available', False)]:
            result = P.read(row['result'])
            result[field] = value
            changed = dict(row, result=self.save(self.root / 'BAD-RESULT.json', result))
            checked, reason = P.completed(changed, self.targets[0])
            self.assertIsNone(checked)
            self.assertIsNotNone(reason)
        result = P.read(row['result'])
        result['CPU']['aggregate_peak_bytes'] += 1
        changed = dict(row, result=self.save(self.root / 'BAD-RESULT.json', result))
        self.assertIsNone(P.completed(changed, self.targets[0])[0])

    def test_bad_formula_and_tampered_job_claim_refuse(self):
        row = dict(self.rows[0], formula='round_to_8GiB')
        self.assertIsNone(P.completed(row, self.targets[0])[0])
        job = self.jobs[0]
        sized = P.apply_job(job, self.rows, self.workload(job))
        sized['claim_bytes'] += 1
        with self.assertRaisesRegex(ValueError, 'claim or physical fence'):
            P.validate_job(sized)

    def test_unapproved_inventory_or_authority_refuses(self):
        for name in ['targets', 'authority']:
            row = deepcopy(self.rows[0])
            row[name]['sha256'] = '0' * 64
            with self.subTest(name=name):
                try:
                    checked, _ = P.completed(row, self.targets[0])
                except ValueError:
                    continue
                self.assertIsNone(checked)

    def test_accounting_requires_exact_job_directory_and_bytes(self):
        row = deepcopy(self.rows[0])
        accounting = P.read(row['accounting'])
        row['accounting'] = self.save(self.root / 'CPU-FINAL.json', accounting)
        self.assertIsNone(P.completed(row, self.targets[0])[0])

    def test_extra_source_change_and_wrong_original_refuse(self):
        row = deepcopy(self.rows[0])
        row['original_source'] = self.rows[1]['original_source']
        self.assertIsNone(P.completed(row, self.targets[0])[0])
        source = self.root / 'Changed.v'
        source.write_bytes(Path(self.rows[0]['native_source']['path']).read_bytes() + b'\n')
        row = dict(self.rows[0], native_source=binding(source))
        self.assertIsNone(P.completed(row, self.targets[0])[0])

    def test_6974_rejects_a_measured_row(self):
        job = next(row for row in self.jobs if row['key'] == '800d6974')
        row = dict(self.rows[0], block=job['key'])
        checked, reason = P.completed(row, job['target'])
        self.assertIsNone(checked)
        self.assertIn('full-fence', reason)

    def test_new_target_file_keeps_the_reviewed_bytes(self):
        path = Path(__file__).with_name('policies') / 'PORT-V34-TARGETS16.json'
        self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),
                         '3df54454cb2ca9337d0441e51f4ad3ef1fcc4bab54285d37301cf0d12a90fd12')

    def test_actual_public_import_and_dependency_planning_match_the_profile(self):
        import scratch
        from entry_chain_stage import import_commands
        row = self.rows[0]
        case = next(case for case in self.authorities[23]['cases'] if case['block'] == row['block'])
        path = Path(row['native_source']['path'])
        self.assertEqual(path.read_bytes(), P.v34_native_caller(self.rules, self.policy, case['source']))
        text = path.read_text()
        modules = {name: name + '.v' for _, names in import_commands(text) for name in names}
        modules['ZesuSsz.Automation.Sets.V34Candidates'] = 'V34Candidates.v'
        edges = scratch.canonical_edges(row['module'], text, None, [], modules)
        self.assertIn({'from': row['module'], 'to': 'ZesuSsz.Evidence.RuleScratchRules'}, edges)
        carrier = scratch.canonical_edges('ZesuSsz.Evidence.RuleScratchRules',
            Path(self.rules['path']).read_text(), None, [], modules)
        self.assertEqual(carrier, [{'from': 'ZesuSsz.Evidence.RuleScratchRules',
                                   'to': 'ZesuSsz.Automation.Sets.V34Candidates'}])
        sized = P.apply_job(self.jobs[0], self.rows, self.workload(self.jobs[0]))
        self.assertEqual(P.validate_job(sized), P.GIB)

    def test_new_comparison_keeps_its_own_bank_and_full_fence(self):
        profile = dict(self.profile, memory_booking=P.PORT_FULL_FENCE_BOOKING,
                       comparison_authority=self.comparison)
        profile.pop('completed_peak_authority')
        bound = self.save(self.root / 'NEW-PROFILE.json', profile)
        job = next(job for job in self.jobs if job['key'] == '800d6a00')
        workload = P.workload_for_job(bound, job, self.context(job, 'NEW'))
        sized = P.apply_job(job, [], workload)
        self.assertEqual(P.validate_job(sized), P.PORT_FENCE)
        self.assertEqual(sized['physical_fence_bytes'], P.PORT_FENCE)
        self.assertIsNone(sized['completed_stock_measurement'])
        self.assertEqual(port_native_policy.cpu_budgets(sized), (None, None))

    def test_swapped_old_new_bank_refuses_with_identical_caller(self):
        job = next(job for job in self.jobs if job['key'] == '800d6a00')
        caller = Path(self.staged[job['key']]['path']).read_bytes()
        with self.assertRaisesRegex(ValueError, 'A memory evidence binding changed|actual workload source differs'):
            P.workload_for_job(self.profile_binding, job, self.context(job, 'NEW'))
        profile = dict(self.profile, memory_booking=P.PORT_FULL_FENCE_BOOKING,
                       comparison_authority=self.comparison)
        profile.pop('completed_peak_authority')
        bound = self.save(self.root / 'NEW-PROFILE.json', profile)
        with self.assertRaisesRegex(ValueError, 'A memory evidence binding changed|actual workload source differs'):
            P.workload_for_job(bound, job, self.context(job, 'OLD'))
        self.assertEqual(Path(self.staged[job['key']]['path']).read_bytes(), caller)

    def test_retention_bank_applies_only_to_the_two_authorized_cases(self):
        for block in ['800d6aa8', '800d6ab4', '800d6a64', '800d6a78']:
            job = next(job for job in self.jobs if job['key'] == block)
            self.workload(job)
            wrong = self.context(job)
            module = 'ZesuSsz.Generated.DecodeItem.MachinePilot180Entries'
            variant = 'OLD' if block in {'800d6aa8', '800d6ab4'} else 'RETENTION'
            wrong['proof_runtime']['module_files'][module] = str(self.bank_files[module][variant])
            with self.assertRaisesRegex(ValueError, 'A memory evidence binding changed|actual workload source differs'):
                P.workload_for_job(self.profile_binding, job, wrong)

    def test_approved_v31_peaks_do_not_imply_successful_proof_returns(self):
        for row, target in zip(self.rows, self.targets):
            if row['block'] not in {'800d6a14', '800d6ab4'}:
                continue
            checked, reason = P.completed(row, target)
            self.assertIsNone(reason)
            self.assertEqual(checked['provenance_version'], 'v3.1')
            self.assertIn('does not establish proof acceptance', checked['qualification'])
            self.assertNotIn('normal_tactic_return', P.read(row['result']))

    def test_arbitrary_or_moved_rules_import_cannot_qualify(self):
        row = self.rows[0]
        text = Path(row['native_source']['path']).read_text()
        line = 'Require Import ZesuSsz.Evidence.RuleScratchRules.\n'
        for changed in [text.replace(line, 'Require Import Other.Rules.\n'),
                        line + text.replace(line, ''), text.replace(line, '') + line,
                        text.replace(line, line + line)]:
            source = self.root / 'BadImport.v'
            source.write_text(changed)
            candidate = dict(row, native_source=binding(source))
            target = dict(self.targets[0], source_sha256=candidate['native_source']['sha256'])
            self.assertIsNone(P.completed(candidate, target)[0])


if __name__ == '__main__':
    unittest.main()
