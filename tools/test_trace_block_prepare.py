"""Test source-preserving diagnostic preparation without native proof runs."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
import trace_block_prepare as prepare

STOP = {"kind": "goal-head", "value": "mem_mapsto_kind"}


class InstrumentationTests(unittest.TestCase):
    def test_all_real_return_hints_keep_exact_bodies(self):
        source = (prepare.OWNER / "ZesuSsz/Automation/ReturnRoute.v").read_text()
        result, entries = prepare.instrument_return_route(source, STOP)
        self.assertEqual(set(entries), {"ReturnRoute.normalize", "ReturnRoute.fault", "ReturnRoute.implication"})
        self.assertEqual(result.count("trace_block_filtered"), 3)
        self.assertEqual(result.count("Hint Extern"), source.count("Hint Extern"))
        for entry in entries.values():
            body = entry["commands"]["whole-rule"]
            self.assertIn(body, source)
            self.assertIn("ltac1:(" + body + ")", result)
            self.assertEqual(entry["commands"]["liShow"], "liShow")
            self.assertIn("requested-trigger", entry["commands"])
        self.assertTrue(result.startswith("From P0Filtered Require Import TraceObserver."))

    def test_unreviewed_return_entry_count_is_rejected(self):
        source = (prepare.OWNER / "ZesuSsz/Automation/ReturnRoute.v").read_text()
        with self.assertRaisesRegex(ValueError, "exactly three"):
            prepare.instrument_return_route("", STOP)
        with self.assertRaisesRegex(ValueError, "extra"):
            prepare.instrument_return_route(source + "\n#[export] Hint Extern 5 True => exact I : typeclass_instances.\n", STOP)

    def test_hooks_keep_original_body_and_alternative_order(self):
        source = (prepare.OWNER / "ZesuSsz/Automation/Hooks.v").read_text()
        result, entries, step = prepare.instrument_hooks(source, {"kind": "rule", "value": "ConjunctMatch"}, True)
        self.assertEqual(list(entries), ["Hooks.zesu_conjunct_head_if_enabled"])
        body = entries["Hooks.zesu_conjunct_head_if_enabled"]["commands"]["whole-rule"]
        self.assertIn(body, source)
        self.assertIn("ltac1:(" + body + ")", result)
        self.assertIn(step, source)
        self.assertIn('trace_block_checkpoint "instruction-lookup"', result)
        self.assertNotIn('trace_block_snapshot', result)
        self.assertIn("end;" + step, result)
        self.assertIn("find_in_context (FindInstrKind _ _) _", result)
        self.assertEqual(result.count("trace_block_filtered"), 1)

    def test_unselected_conjunct_entry_is_unchanged(self):
        source = (prepare.OWNER / "ZesuSsz/Automation/Hooks.v").read_text()
        result, entries, _ = prepare.instrument_hooks(source, {"kind": "instruction", "value": "jalr"}, False)
        self.assertEqual(entries, {})
        self.assertNotIn("trace_block_filtered", result)
        self.assertIsNotNone(prepare.trigger_guard({"kind": "instruction", "value": "jalr"}))

    def test_scanner_retains_qualified_names_strings_and_nested_comments(self):
        source = '(* nested (* x. *) end *)\nLtac t := idtac "message.with.dot."; A.b.\nCheck True.\n'
        commands = [source[a:b] for a, b in prepare.command_spans(source)]
        self.assertEqual(len(commands), 2)
        self.assertIn('A.b.', commands[0])
        self.assertEqual(commands[1].strip(), 'Check True.')
        with self.assertRaisesRegex(ValueError, "unclosed"):
            list(prepare.command_spans('(* unfinished'))

    def test_commented_definition_does_not_create_a_false_match(self):
        source = '(* Ltac chosen := invalid. *)\nLtac other := idtac.\nLtac chosen := exact I.\n'
        changed, body = prepare.replace_ltac(source, 'chosen', lambda code: '(' + code + ')')
        self.assertEqual(body, ' exact I')
        self.assertIn('(* Ltac chosen := invalid. *)', changed)
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            prepare.replace_ltac(source + 'Ltac chosen := fail.\n', 'chosen', lambda code: code)

    def test_copy_preserves_dirty_bytes_modes_and_deletions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, destination = root / 'source', root / 'copy'
            source.mkdir(); destination.mkdir()
            (source / 'dirty.v').write_bytes(b'changed\r\n')
            (source / 'dirty.v').chmod(0o755)
            (source / 'link').symlink_to('dirty.v')
            (destination / 'deleted.v').write_text('old')
            inventory = {'dirty.v': {'sha256': prepare.digest(source / 'dirty.v'), 'mode': 0o755},
                         'link': {'symlink': 'dirty.v'}, 'deleted.v': {'deleted': True}}
            prepare.copy_inventory(source, destination, inventory)
            self.assertEqual((destination / 'dirty.v').read_bytes(), b'changed\r\n')
            self.assertEqual((destination / 'dirty.v').stat().st_mode & 0o777, 0o755)
            self.assertTrue((destination / 'link').is_symlink())
            self.assertFalse((destination / 'deleted.v').exists())
            (source / 'dirty.v').write_text('later')
            with self.assertRaisesRegex(ValueError, "changed"):
                prepare.copy_inventory(source, destination, inventory)

    def test_dependency_environment_keeps_normal_fences(self):
        environment = prepare.build_environment(Path('/tmp/owned'), 'fixture-writer')
        self.assertEqual(environment['ZESU_MODULE_LIMIT_GIB'], '6')
        self.assertEqual(environment['ZESU_PROOF_CPU_LIMIT'], '1200')
        self.assertEqual(environment['ZESU_WRITER_ID'], 'fixture-writer')
        self.assertNotIn('ZESU_DIAGNOSTIC_PROBE', environment)


class CorrectionTests(unittest.TestCase):
    def test_all_remains_first_and_declaration_bytes_remain(self):
        source = '(* retained *)\nRequire Import ZesuSsz.Automation.All.\nLemma x : True.\nProof.\n'
        changed = prepare.insert_bridge_import(source)
        self.assertEqual(changed.replace('\nFrom P0Filtered Require Import TraceObserver.', ''), source)
        self.assertLess(changed.index('Automation.All'), changed.index('P0Filtered'))
        with self.assertRaisesRegex(ValueError, 'All first'):
            prepare.insert_bridge_import('Require Import X.\nLemma x : True.\nProof.\n')

    def test_masked_return_guard_retains_both_shapes(self):
        guard = prepare.trigger_guard({'kind': 'instruction', 'value': 'jalr'})
        self.assertIn('(bv_add _ (BV 64 0))', guard)
        self.assertIn('(bv_and _ (BV 64 18446744073709551614))', guard)

    def test_requested_stop_checkpoint_preserves_original_step(self):
        source = (prepare.OWNER / 'ZesuSsz/Automation/Hooks.v').read_text()
        for stop in ({'kind':'instruction', 'value':'WriteMem'},
                     {'kind':'instruction', 'value':'FindMemMapsTo'},
                     {'kind':'goal-head', 'value':'mem_mapsto_kind'},
                     {'kind':'pc', 'value':'0x800d69b0'}):
            with self.subTest(stop=stop):
                result, entries, body = prepare.instrument_hooks(source, stop, False)
                self.assertIn('trace_block_checkpoint "requested-trigger"', result)
                self.assertIn('else idtac;' + body, result)
                self.assertEqual(entries, {})
                self.assertIn(body, source)

    def test_pc_guard_cannot_assign_address(self):
        guard = prepare.trigger_guard({'kind':'pc', 'value':'0x800d69b0'})
        self.assertIn('FindInstrKind ?address _', guard)
        self.assertIn('assert_fails (has_evar address)', guard)
        self.assertIn('constr_eq address expected', guard)
        self.assertIn(str(int('800d69b0', 16)) + '%Z', guard)
        self.assertNotIn('unify', guard)

    def test_goal_head_guard_does_not_guess_application_arity(self):
        guard = prepare.trigger_guard({'kind':'goal-head', 'value':'mem_mapsto_kind'})
        self.assertIn('envs_entails _ ?body', guard)
        self.assertIn('let rec head', guard)
        self.assertIn('constr_eq actual mem_mapsto_kind', guard)

    def test_original_return_prefix_operations_are_named(self):
        for client in ('ReturnRoute.normalize', 'ReturnRoute.fault', 'ReturnRoute.implication'):
            commands = dict(prepare.return_clause_commands(client))
            self.assertEqual(list(commands), ['switch-check', 'closed-ra', 'zesu_return_decode_facts',
                'alignment-selector-after-decode', 'address-selection'])
            self.assertIn('assert_fails (has_evar ra)', commands['closed-ra'])
            self.assertIn('zesu_return_decode_facts', commands['alignment-selector-after-decode'])
            self.assertIn('(?address mod 4 = 0)%Z', commands['alignment-selector-after-decode'])
            self.assertIn('zesu_return_with_address ra', commands['address-selection'])
            self.assertNotIn('decodeItem', ''.join(commands.values()))

    def test_native_inventory_binds_ignored_bytes_and_rejects_empty(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with self.assertRaisesRegex(ValueError, 'empty'):
                prepare.native_inventory(root)
            (root / 'index.v').write_bytes(b'opaque\r\n')
            first = prepare.native_inventory(root)
            self.assertEqual(first, {'index.v': prepare.digest(root / 'index.v')})
            (root / 'index.v').write_bytes(b'changed\n')
            self.assertNotEqual(prepare.native_inventory(root), first)


class PreparedRegistryTests(unittest.TestCase):
    def test_uncompiled_record_is_not_published(self):
        with self.assertRaisesRegex(ValueError, "has not passed"):
            prepare.publish_prepared({}, {})

    def test_corrected_lookup_checks_sources_and_objects(self):
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'scope/source.v'; source.parent.mkdir()
            source.write_text('source')
            obj = root / 'scope/_build/agents/test/source.vo'; obj.parent.mkdir(parents=True)
            obj.write_bytes(b'object')
            request = {'scope': {'root': 'a' * 40}, 'rule_set': [], 'stop': {'kind': 'residual'}}
            original = root / 'original'; original.mkdir()
            import subprocess
            subprocess.run(['git', 'init', '-q', str(original)], check=True)
            native = original / 'generated/isla-traces'; native.mkdir(parents=True)
            (native / 'index.v').write_text('exact native bytes')
            (original / 'facts.v').write_text('exact frozen source')
            inventory = root / 'ORIGINAL-SOURCES.json'
            native_inventory = root / 'ORIGINAL-NATIVE-SOURCES.json'
            prepare.save(inventory, prepare.source_inventory(original))
            prepare.save(native_inventory, prepare.native_inventory(native))
            descriptors = {'ReturnRoute.normalize': {'rule': 'ReturnRoute', 'commands': {}}}
            guard_reference = prepare.install_guard_manifest(source.parent, descriptors)
            for name in ('install/default/lib/p0-filtered-trace/trace-observer/filtered_trace_plugin.cmxs',
                         'default/' + prepare.package.BRIDGE.replace('.v', '.vo'),
                         'default/' + prepare.package.WRITER_TARGET):
                path = obj.parent/name
                path.parent.mkdir(parents=True,exist_ok=True)
                path.write_bytes(b'compiled fixture artifact')
            runtime = prepare.package.runtime_inputs(source.parent,obj.parent)
            record = dict(request, **runtime, workspace=str(source.parent), build_dir=str(obj.parent),
                entry_descriptors=descriptors, guard_manifest=guard_reference,
                instrumentation={'protocol': 'filtered-chunks-v1',
                    'prepared_source_hashes': {'source.v': prepare.digest(source)}},
                preparation_evidence={'original_workspace': str(original),
                    'original_sources': str(inventory), 'original_sources_sha256': prepare.digest(inventory),
                    'original_native_sources': str(native_inventory),
                    'original_native_sources_sha256': prepare.digest(native_inventory)},
                focused_compilation={'success': True, 'objects': {'source.vo': prepare.digest(obj)}})
            with patch.object(prepare, 'OWNER', root):
                self.assertIsNone(prepare.corrected_prepared(request))
                prepare.publish_prepared(request, record)
                self.assertEqual(prepare.corrected_prepared(request), record)
                obj.write_bytes(b'changed')
                with self.assertRaisesRegex(ValueError, 'artifact changed'):
                    prepare.corrected_prepared(request)
                obj.write_bytes(b'object'); source.write_text('changed')
                with self.assertRaisesRegex(ValueError, 'source changed'):
                    prepare.corrected_prepared(request)
                source.write_text('source')
                import copy
                legacy = copy.deepcopy(record)
                legacy['instrumentation'].pop('protocol')
                path = root / '_build/trace-preparation/corrected' / (prepare.request_key(request) + '.json')
                path.write_text(json.dumps(legacy))
                with self.assertRaisesRegex(ValueError, 'filtered capture protocol'):
                    prepare.corrected_prepared(request)
                path.write_text(json.dumps(record))
                (original / 'facts.v').write_text('changed original dependency')
                with self.assertRaisesRegex(ValueError, 'original frozen inventory changed'):
                    prepare.corrected_prepared(request)

    def test_affected_chain_is_topological_and_ignores_unaffected_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for module, text in {'A': 'Require Import B C.\n', 'B': 'Require Export D.\n',
                                 'C': '', 'D': ''}.items():
                (root / (module + '.v')).write_text(text)
            self.assertEqual(prepare.affected_modules(root, ['A'], ['D']), ['D', 'B', 'A'])
            (root / 'D.v').write_text('Require Import A.\n')
            with self.assertRaisesRegex(ValueError, 'cycle'):
                prepare.affected_modules(root, ['A'], ['D'])


class ReviewOwnershipTests(unittest.TestCase):
    def test_writer_identity_has_no_fixed_agent_default(self):
        from unittest.mock import patch
        with patch.dict(prepare.os.environ, {}, clear=True):
            with self.assertRaisesRegex(ValueError, 'writer identity'):
                prepare.writer_identity()
            for writer in ('../other', '.', '..', 'a/b', 'a b', 'x$y'):
                with self.subTest(writer=writer), self.assertRaises(ValueError):
                    prepare.writer_identity({'writer_id': writer})
            self.assertEqual(prepare.writer_identity({'writer_id': 'owned-worker'}), 'owned-worker')
        with patch.dict(prepare.os.environ, {'COORD_AGENT': 'coord-worker'}, clear=True):
            self.assertEqual(prepare.writer_identity(), 'coord-worker')
        with patch.dict(prepare.os.environ, {'ZESU_WRITER_ID': 'named-worker'}, clear=True):
            self.assertEqual(prepare.writer_identity(), 'named-worker')

    def test_refresh_preserves_off_removal_and_on_addition(self):
        import shutil
        import subprocess
        for enabled in (False, True):
            with self.subTest(enabled=enabled), tempfile.TemporaryDirectory() as directory:
                root = Path(directory); original = root / 'original'; original.mkdir()
                subprocess.run(['git', 'init', '-q', str(original)], check=True)
                for name, text in {
                    'ZesuSsz/Automation/Hooks.v': 'Ltac zesu_liAStep := idtac.\n',
                    'ZesuSsz/Automation/All.v': '',
                    'ZesuSsz/Automation/ReturnRoute.v': (prepare.OWNER / 'ZesuSsz/Automation/ReturnRoute.v').read_text(),
                    'ZesuSsz/Evidence/TraceObserver.v': '',
                    'Switch.v': '' if enabled else '#[export] Instance enabled : ZesuStepReturnRoute := I.\n',
                    'generated/isla-traces/index.v': 'exact native bytes',
                    prepare.PLUGIN + '/trace-observer/filtered_trace_plugin.ml': 'old plugin'}.items():
                    target = original / name; target.parent.mkdir(parents=True, exist_ok=True); target.write_text(text)
                declaration = 'Lemma target : True.\n'
                prefix = 'Require Import ZesuSsz.Automation.All.\nRequire Import Switch.\n' + declaration + 'Proof.\n'
                source = original / 'Block.v'; source.write_text(prefix + 'Abort.\n')
                request = {'workspace': str(original), 'source': str(source), 'source_prefix': prefix,
                    'declaration': declaration, 'scope': {'source_sha256': prepare.digest(source)},
                    'rule_set': [{'name': 'ReturnRoute', 'enabled': enabled}],
                    'stop': {'kind': 'residual', 'value': None}, 'writer_id': 'fixture-owner'}
                owned = root / 'owned'; shutil.copytree(original, owned, ignore=shutil.ignore_patterns('.git'))
                scratch = owned / '_build/trace-native/Block.v'; scratch.parent.mkdir(parents=True)
                scratch.write_text(prefix + 'Abort.\n')
                build = owned / '_build/agents/fixture-owner'; (build / 'default').mkdir(parents=True)
                inputs = root / 'INPUTS.json'; prepare.save(inputs, {'inventory': prepare.source_inventory(original)})
                names = ['ZesuSsz/Automation/Hooks.v', 'ZesuSsz/Automation/ReturnRoute.v',
                         prepare.PLUGIN + '/trace-observer/filtered_trace_plugin.ml', '_build/trace-native/Block.v']
                for name in ('install/default/lib/p0-filtered-trace/trace-observer/filtered_trace_plugin.cmxs',
                             'default/' + prepare.package.BRIDGE.replace('.v','.vo'),
                             'default/' + prepare.package.WRITER_TARGET):
                    artifact=build/name
                    artifact.parent.mkdir(parents=True,exist_ok=True)
                    artifact.write_bytes(b'compiled fixture artifact')
                runtime=prepare.package.runtime_inputs(owned,build)
                previous = dict(request, **runtime, workspace=str(owned), source=str(scratch), build_dir=str(build),
                    selected_rules=['ReturnRoute'], instrumentation={'protocol':'filtered-chunks-v1', 'original_scope_record': str(inputs),
                    'original_scope_sha256': prepare.digest(inputs),
                    'prepared_source_hashes': {name: prepare.digest(owned / name) for name in names}})
                completed = root / 'PREPARED.json'; prepare.save(completed, previous)
                plugin = root / 'new.ml'; plugin.write_text('new plugin')
                expected_prefix, adjustments = prepare.switch_adjusted_prefix(owned, request)
                result = prepare.refresh_preparation(request, completed, root / 'refresh', plugin)
                self.assertEqual(scratch.read_text(), prepare.insert_bridge_import(expected_prefix) + 'Abort.\n')
                self.assertEqual(result['instrumentation']['switch_adjustments'], adjustments)
                expected = '#[local] Instance : ZesuStepReturnRoute := I.' if enabled else 'Remove Hints Switch.enabled : typeclass_instances.'
                self.assertEqual(scratch.read_text().count(expected), 1)
                self.assertEqual(result['writer_id'], 'fixture-owner')
                self.assertIs(result['focused_compilation']['success'], False)
                self.assertIn(prepare.BRIDGE.replace('.v','.vo'), result['focused_targets'])
                self.assertEqual((root / 'refresh/before/_build/trace-native/Block.v').read_text(), prefix + 'Abort.\n')


if __name__ == '__main__':
    unittest.main()
