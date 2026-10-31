import ast
import asyncio
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import traceback
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE / 'code'), str(HERE)]
import scratch
import scratch_limits as limits
from entry_chain import save
import memory_policy


class SearchWindowControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        parent = self.root / 'zesuworkloads.slice'
        parent.mkdir()
        (parent / 'memory.max').write_text(str(175 * 1024**3))
        (parent / 'memory.swap.max').write_text('0')
        self.group = parent / 'zesuworkloads-aggregate1000p1r2.slice'
        self.group.mkdir()
        for name, value in {'memory.max': str(64 * 1024**3), 'memory.swap.max': '0',
                            'memory.current': '100', 'memory.peak': '200',
                            'memory.events': 'oom 0\noom_kill 0\nmax 0\n'}.items():
            (self.group / name).write_text(value)
        self.cpu(1000)
        stat = self.group.stat()
        self.identity = {'aggregate_path': str(self.group), 'aggregate_device': stat.st_dev,
                         'aggregate_inode': stat.st_ino, 'inside_pid': 1, 'inside_startticks': 2}
        self.out = self.root / 'job'
        self.out.mkdir()
        self.memory_job=memory_policy.apply_job({'phase':'native','target':{}})
        save(self.out/'RUNTIME.json',{'canonical_admission':{'memory_job':self.memory_job}})
        save(self.out / 'BATCH-IDENTITY.json', self.identity)
        self.arguments = {'from_state': 1, 'body': 'zesu_block.', 'timeout': 604800}

    def cpu(self, value):
        (self.group / 'cpu.stat').write_text('usage_usec ' + str(int(value * 1e6)) + '\n')

    def test_stock_fence_and_window(self):
        self.assertEqual(limits.CPU_STOP_SECONDS, 7200)
        self.assertEqual(limits.MEMORY_FENCE_BYTES, 64 * 1024**3)
        attempt = scratch.full_fence_attempt({'limits': {}, 'scope_limits': [
            {'role': role} for role in ['aggregate', 'batch', 'client', 'mcp', 'pet', 'compiler']]})
        for row in attempt['scope_limits']:
            self.assertEqual(row['memory_bytes'], (175 if row['role'] == 'workloads' else 64) * 1024**3)
            self.assertEqual(row['swap_bytes'], 0)

    def test_prospective_module_limits_match_actual_launch(self):
        env=memory_policy.environment('native',64*1024**3,job=self.memory_job)
        self.assertEqual(env['ZESU_MODULE_LIMIT_GIB'],'64')
        self.assertEqual(env['ZESU_GATE_MODULE_LIMIT_GIB'],'64')
        self.assertEqual(env['ZESU_AGGREGATE_LIMIT'],'64G')
        source=(HERE/'code/stage1_runtime.py').read_text()
        self.assertIn("environment(job['phase'],job['claim_bytes'],job=job)",source)
        for rel in ['code/entry_chain_run.py', 'code/stage1_runtime.py']:
            tree = ast.parse((HERE / rel).read_text())
            calls = [node for node in ast.walk(tree) if isinstance(node, ast.Call)]
            for call in calls:
                for keyword in call.keywords:
                    if keyword.arg == 'ZESU_MODULE_LIMIT_GIB':
                        self.assertEqual(ast.literal_eval(keyword.value), env['ZESU_MODULE_LIMIT_GIB'])
                    if keyword.arg == 'ZESU_BATCH_LIMIT':
                        self.assertEqual(ast.literal_eval(keyword.value), env['ZESU_AGGREGATE_LIMIT'])

    def test_absent_origin_does_not_charge_setup_as_search(self):
        self.assertIsNone(limits.stop_reason(1000, 0, 64 * 1024**3, 9000))
        result = limits.search_accounting(self.out, self.identity, 1000)
        self.assertFalse(result['search_started'])
        self.assertEqual(result['setup_CPU_seconds'], 1000)
        self.assertIsNone(result['search_CPU_seconds'])

    def test_late_origin_gets_the_complete_search_window(self):
        limits.record_search_origin(self.out, 123, self.arguments)
        result = limits.search_accounting(self.out, self.identity, 8199.999)
        self.assertIsNone(limits.stop_reason(8199.999, 0, 1, origin_cpu=result['origin_cpu']))
        self.assertEqual(limits.stop_reason(8200, 0, 1, origin_cpu=result['origin_cpu']), 'external_CPU_stop')
        self.assertEqual(limits.stop_reason(8200.5, 0, 1, origin_cpu=result['origin_cpu']), 'external_CPU_stop')

    def test_prerequisites_use_the_separate_setup_budget(self):
        self.assertIsNone(limits.stop_reason(120, 0, 1, phase='prerequisites'))
        self.assertIsNone(limits.stop_reason(2000, 0, 1, phase='prerequisites'))
        self.assertIsNone(limits.stop_reason(7200, 0, 1, phase='prerequisites'))

    def test_returned_search_does_not_charge_later_compilation(self):
        self.assertIsNone(limits.stop_reason(5000, 0, 1, origin_cpu=1000, end_cpu=1050))

    def test_physical_fence_applies_before_the_origin(self):
        self.assertEqual(limits.stop_reason(1, 64 * 1024**3, 1), 'external_memory_stop')

    def test_limit_loop_stops_after_7200_search_cpu_seconds(self):
        limits.record_search_origin(self.out, 123, self.arguments)
        self.cpu(8200)

        class Child:
            def poll(self):
                return None

            def wait(self):
                return -15

        class StopReply:
            returncode = 0
            stdout = ''
            stderr = ''

        with patch.object(limits.subprocess, 'run', return_value=StopReply()) as stop:
            self.assertEqual(limits.wait_with_limits(Child(), self.out, 64 * 1024**3), -15)
        stop.assert_called_once_with(['/usr/bin/systemctl', '--user', 'stop', self.group.name],
                                     capture_output=True, text=True)
        record = json.loads((self.out / 'EXTERNAL-STOP.json').read_text())
        self.assertEqual(record['reason'], 'external_CPU_stop')
        self.assertEqual(record['setup_CPU_seconds'], 1000)
        self.assertEqual(record['search_CPU_seconds'], 7200)
        final = json.loads((self.out / 'CPU-FINAL.json').read_text())
        self.assertEqual(final['CPU_budget_scope'], 'native_search')

    def test_limit_loop_without_origin_does_not_stop_at_120_total(self):
        class Child:
            count = 0

            def poll(self):
                self.count += 1
                return None if self.count == 1 else 0

            def wait(self):
                return 0

        with patch.object(limits.subprocess, 'run') as stop, patch.object(limits.time, 'sleep'):
            self.assertEqual(limits.wait_with_limits(Child(), self.out, 64 * 1024**3), 0)
        stop.assert_not_called()
        self.assertFalse((self.out / 'EXTERNAL-STOP.json').exists())

    def test_wrong_physical_fence_refuses(self):
        (self.group / 'memory.max').write_text(str(24 * 1024**3))
        with self.assertRaises(ValueError):
            limits.record_search_origin(self.out, 123, self.arguments)

    def test_origin_cannot_reset(self):
        limits.record_search_origin(self.out, 123, self.arguments)
        self.cpu(1100)
        with self.assertRaises(ValueError):
            limits.record_search_origin(self.out, 124, self.arguments)

    def test_origin_identity_mismatch_refuses(self):
        limits.record_search_origin(self.out, 123, self.arguments)
        with self.assertRaises(ValueError):
            limits.search_accounting(self.out, dict(self.identity, inside_startticks=3), 1100)

    def test_changed_native_command_refuses(self):
        with self.assertRaises(ValueError):
            limits.record_search_origin(self.out, 123, dict(self.arguments, body='idtac.'))

    def test_decreasing_cpu_counter_refuses(self):
        limits.record_search_origin(self.out, 123, self.arguments)
        with self.assertRaises(ValueError):
            limits.search_accounting(self.out, self.identity, 999)

    def test_origin_publication_is_atomic(self):
        partial = threading.Event()
        finish = threading.Event()
        errors = []
        final = self.out / 'SEARCH-CPU-ORIGIN.json'

        def delayed_dump(value, stream, **kwargs):
            stream.write('{"partial":')
            stream.flush()
            partial.set()
            if not finish.wait(10):
                raise RuntimeError('The control did not release serialization.')
            stream.seek(0)
            stream.truncate()
            original_dump(value, stream, **kwargs)

        def writer():
            try:
                limits.record_search_origin(self.out, 123, self.arguments)
            except BaseException as error:
                errors.append(error)

        original_dump = json.dump
        with patch.object(json, 'dump', side_effect=delayed_dump):
            thread = threading.Thread(target=writer)
            thread.start()
            try:
                self.assertTrue(partial.wait(10))
                self.assertFalse(final.exists())
            finally:
                finish.set()
                thread.join(10)
            self.assertFalse(thread.is_alive())
            self.assertEqual(errors, [])
        self.assertEqual(json.loads(final.read_text())['CPU_seconds'], 1000)

    def test_actual_provider_publishes_before_rpc_and_ends_after_return(self):
        # Execute the provider's actual nested call function with a nonproof RPC.
        source = ast.parse((HERE / 'code/entry_chain_provider.py').read_text())
        outer = next(node for node in source.body if isinstance(node, ast.AsyncFunctionDef) and node.name == 'execute')
        function = next(node for node in outer.body if isinstance(node, ast.AsyncFunctionDef) and node.name == 'call')
        output = self.out / 'native'
        output.mkdir()
        namespace = {'runtime': {'phase': 'native'}, 'native_body': 'zesu_block.', 'output': output, 'calls': [],
                     'check_operation': lambda runtime, **kwargs: {}, 'atomic_json': save,
                     'time': time, 'traceback': traceback, 'ToolFailure': RuntimeError}
        exec(compile(ast.fix_missing_locations(ast.Module(body=[function], type_ignores=[])), '<provider-call>', 'exec'), namespace)
        control = self

        class Reply:
            structuredContent = {'success': True}
            isError = False

            def model_dump(self, **kwargs):
                return {'structuredContent': self.structuredContent}

        class Session:
            async def call_tool(self, name, arguments):
                origin = json.loads((control.out / 'SEARCH-CPU-ORIGIN.json').read_text())
                control.assertEqual(origin['CPU_seconds'], 1000)
                control.assertEqual(origin['arguments'], control.arguments)
                control.assertFalse((control.out / 'SEARCH-CPU-END.json').exists())
                control.cpu(1050)
                return Reply()

        result = asyncio.run(namespace['call'](Session(), 'rocq_check', self.arguments))
        self.assertTrue(result['success'])
        end = json.loads((self.out / 'SEARCH-CPU-END.json').read_text())
        self.assertEqual(end['search_CPU_seconds'], 50)
        costs = limits.search_accounting(self.out, self.identity, 1100)
        self.assertEqual(costs['setup_CPU_seconds'], 1000)
        self.assertEqual(costs['search_CPU_seconds'], 50)
        self.assertEqual(costs['post_search_CPU_seconds'], 50)

    def test_returned_native_search_followed_by_qed_keeps_one_origin(self):
        source = ast.parse((HERE / 'code/entry_chain_provider.py').read_text())
        outer = next(node for node in source.body if isinstance(node, ast.AsyncFunctionDef) and node.name == 'execute')
        function = next(node for node in outer.body if isinstance(node, ast.AsyncFunctionDef) and node.name == 'call')
        output = self.out / 'native'
        output.mkdir()
        namespace = {'runtime': {'phase': 'native'}, 'native_body': 'zesu_block.', 'output': output, 'calls': [],
                     'check_operation': lambda runtime, **kwargs: {}, 'atomic_json': save,
                     'time': time, 'traceback': traceback, 'ToolFailure': RuntimeError}
        exec(compile(ast.fix_missing_locations(ast.Module(body=[function], type_ignores=[])), '<provider-call>', 'exec'), namespace)
        control = self

        class Reply:
            structuredContent = {'success': True}
            isError = False

            def model_dump(self, **kwargs):
                return {'structuredContent': self.structuredContent}

        class Session:
            async def call_tool(self, name, arguments):
                control.cpu(1050 if arguments['body'] == 'zesu_block.' else 1100)
                return Reply()

        async def sequence():
            session = Session()
            await namespace['call'](session, 'rocq_check', self.arguments)
            origin = (self.out / 'SEARCH-CPU-ORIGIN.json').read_bytes()
            end = (self.out / 'SEARCH-CPU-END.json').read_bytes()
            await namespace['call'](session, 'rocq_check', dict(self.arguments, body='Qed.'))
            self.assertEqual((self.out / 'SEARCH-CPU-ORIGIN.json').read_bytes(), origin)
            self.assertEqual((self.out / 'SEARCH-CPU-END.json').read_bytes(), end)

        asyncio.run(sequence())
        self.assertEqual(len(namespace['calls']), 2)
        self.assertEqual(namespace['calls'][-1]['arguments']['body'], 'Qed.')
        costs = limits.search_accounting(self.out, self.identity, 1100)
        self.assertEqual(costs['setup_CPU_seconds'], 1000)
        self.assertEqual(costs['search_CPU_seconds'], 50)
        self.assertEqual(costs['post_search_CPU_seconds'], 50)


if __name__ == '__main__':
    unittest.main()
