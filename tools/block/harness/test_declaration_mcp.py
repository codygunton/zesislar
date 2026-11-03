"""Check level ordering, ordinary receipts, and bounded MCP sessions."""
from contextlib import asynccontextmanager
from pathlib import Path
import tempfile
import asyncio
import json
import unittest
from unittest.mock import patch

from declaration_mcp import levels, run, session_limit
from entry_chain import binding, save


GIB = 1024**3


class LevelTests(unittest.TestCase):
    def test_independent_declarations_share_their_dependency_level(self):
        result, _ = levels(['A', 'B', 'C'], [{'from': 'C', 'to': 'A'}, {'from': 'C', 'to': 'B'}], [])
        self.assertEqual(result, [['A', 'B'], ['C']])

    def test_protected_modules_remain_serial_barriers(self):
        result, _ = levels(['A', 'Protected', 'B'], [], [], ['Protected'])
        self.assertEqual(result, [['A'], ['Protected'], ['B']])

    def test_missing_dependency_refuses(self):
        with self.assertRaisesRegex(ValueError, 'absent dependency'):
            levels(['A'], [{'from': 'A', 'to': 'Missing'}], [])

    def test_cycle_refuses(self):
        with self.assertRaisesRegex(ValueError, 'cycle'):
            levels(['A', 'B'], [{'from': 'A', 'to': 'B'}, {'from': 'B', 'to': 'A'}], [])

    def test_completed_dependencies_do_not_compile_again(self):
        self.assertEqual(levels(['A'], [{'from': 'A', 'to': 'Done'}], ['Done'])[0], [['A']])
        with self.assertRaises(ValueError):
            levels(['A'], [], ['A'])

    def test_historical_controller_and_unmeasured_compiler_allow_one_session(self):
        self.assertEqual(session_limit(8, 64*GIB, 24964177920, [16*GIB], GIB), 1)

    def test_matching_small_compiler_weights_can_allow_two_sessions(self):
        self.assertEqual(session_limit(8, 64*GIB, 24964177920, [GIB], GIB), 2)
        with self.assertRaisesRegex(ValueError, 'do not fit'):
            session_limit(8, 16*GIB, 24964177920, [16*GIB], GIB)


class DispatchTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        graph = self.root / 'GRAPH.json'
        save(graph, {'import_edges': [{'from': 'C', 'to': 'A'}, {'from': 'C', 'to': 'B'}]})
        self.runtime = {'ordered_modules': ['A', 'B', 'C'], 'declaration_dag': {
            'graph': binding(graph), 'completed_modules': [], 'maximum_workers': 8,
            'weights': {'A': GIB, 'B': GIB, 'C': GIB}, 'keep_going': True},
            'canonical_admission': {'physical_fence_bytes': 64*GIB}}
        self.order = []
        self.closed = []
        self.cpu = self.root / 'cpu.stat'
        self.cpu.write_text('usage_usec 1000000\n')

    @asynccontextmanager
    async def session(self, index):
        try:
            yield index
        finally:
            self.closed.append(index)

    async def compile(self, session, name):
        self.order.append(name)
        if name == 'C' and json.loads((self.root/'GRAPH.json').read_text())['import_edges']:
            self.assertTrue({'A', 'B'} <= set(self.order))
        physical = self.root / (name + '-PHYSICAL.json')
        save(physical, {'user_CPU_seconds': 1, 'system_CPU_seconds': 0,
                        'wall_seconds': 1})
        receipt = self.root / (name + '-OBJECT.json')
        save(receipt, {'physical_result': binding(physical)})
        return binding(receipt)

    async def execute(self, compile=None):
        with patch('declaration_mcp.aggregate_root', return_value=self.root):
            return await run(self.runtime, self.root, 0, self.session, compile or self.compile,
                             controller_bytes=24964177920, client_bytes=GIB,
                             normal_failure=lambda error: isinstance(error, ValueError))

    async def test_sample_precedes_dispatch_and_preserves_receipts(self):
        result = await self.execute()
        self.assertEqual(self.order, ['A', 'B', 'C'])
        self.assertEqual(result['completed_modules'], 3)
        self.assertEqual(result['dependency_depth'], 2)
        self.assertEqual(result['sample']['module'], 'A')
        self.assertEqual(self.closed, [1])
        self.assertEqual(set(result['receipts']), {'A', 'B', 'C'})

    async def test_normal_error_blocks_dependent_and_keeps_normal_session_close(self):
        async def fail(session, name):
            if name == 'B':
                raise ValueError('Recorded compiler error')
            return await self.compile(session, name)
        with self.assertRaisesRegex(RuntimeError, 'failed or blocked'):
            await self.execute(fail)
        self.assertEqual(self.order, ['A'])
        self.assertEqual(self.closed, [1])

    async def test_infrastructure_error_stops_later_levels(self):
        async def fail(session, name):
            if name == 'B':
                raise OSError('Changed compiler binding')
            return await self.compile(session, name)
        with self.assertRaisesRegex(OSError, 'Changed compiler'):
            await self.execute(fail)
        self.assertNotIn('C', self.order)
        self.assertEqual(self.closed, [1])

    async def test_high_measured_ratio_stops_before_parallel_dispatch(self):
        async def expensive(session, name):
            reference = await self.compile(session, name)
            self.cpu.write_text('usage_usec 12000000\n')
            return reference
        with self.assertRaisesRegex(RuntimeError, 'ratio exceeds 10'):
            await self.execute(expensive)
        self.assertEqual(self.order, ['A'])
        self.assertEqual(self.closed, [])

    async def test_independent_sessions_overlap_after_the_sample(self):
        self.runtime['ordered_modules'] = ['A', 'B', 'C']
        save(self.root / 'GRAPH.json', {'import_edges': []})
        self.runtime['declaration_dag']['graph'] = binding(self.root / 'GRAPH.json')
        both = asyncio.Event()
        active = set()
        async def overlap(session, name):
            if name != 'A':
                active.add(name)
                if active == {'B', 'C'}:
                    both.set()
                await asyncio.wait_for(both.wait(), 1)
            return await self.compile(session, name)
        result = await self.execute(overlap)
        self.assertTrue(both.is_set())
        self.assertEqual(result['completed_modules'], 3)

    async def test_normal_sample_error_continues_independent_and_blocks_dependent(self):
        attempted = []
        async def fail(session, name):
            attempted.append(name)
            if name == 'A':raise ValueError('Recorded sample compile_error')
            return await self.compile(session, name)
        with self.assertRaisesRegex(RuntimeError, 'failed or blocked'):
            await self.execute(fail)
        report=json.loads((self.root/'MCP-DECLARATIONS.json').read_text())
        self.assertEqual(attempted,['A','B'])
        self.assertEqual(set(report['receipts']),{'B'})
        self.assertEqual(set(report['failures']),{'A'})
        self.assertEqual(report['blocked'],{'C':['A']})
        self.assertFalse(report['sample']['success'])
        self.assertIsNone(report['sample']['compiler_CPU_seconds'])
        self.assertEqual(self.closed,[1])

    async def test_fatal_sample_error_stops_independent_work(self):
        attempted=[]
        async def fail(session,name):
            attempted.append(name)
            raise OSError('Changed compiler binding')
        with self.assertRaisesRegex(OSError,'Changed compiler'):
            await self.execute(fail)
        self.assertEqual(attempted,['A'])
        self.assertEqual(self.closed,[])

    async def test_normal_sample_error_stops_when_keep_going_is_disabled(self):
        self.runtime['declaration_dag']['keep_going']=False
        attempted=[]
        async def fail(session,name):
            attempted.append(name)
            raise ValueError('Recorded sample compile_error')
        with self.assertRaisesRegex(ValueError,'sample compile_error'):
            await self.execute(fail)
        self.assertEqual(attempted,['A'])
