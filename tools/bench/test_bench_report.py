"""Check BENCH run parsing and the report (tools/bench/bench_report.py, bench.py report)."""

import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest

import bench
import bench_report as R

LOG = '''Warning: something
Chars 0 - 60 [Require~Import~ZesuSsz.Generated.X.Entries.] 1.5 secs (1.2u,0.3s)
Chars 61 - 90 [Require~Import~ZesuSsz.Automation2.All.] 2. secs (2.u,0.s)
@@T kind=lia site=premise stage=zesu_run_pass facts=417 nodes=66500 goal_nodes=12 ms=4000 ok=0 cpu_ms=3900
@@T kind=stage site=zesu_run_pass facts=-1 nodes=-1 goal_nodes=-1 ms=50000 ok=1 cpu_ms=50000
Tactic call zesu_run ran for 10.5 secs (10.u,0.5s) (success)
@@T kind=bv_solve site="join entry" stage=zesu_finish_final_pure facts=20 nodes=300 goal_nodes=4 ms=500
 ok=1 cpu_ms=480 ts_us=1000000 rss0_kb=1000 rss1_kb=3000
@@T kind=stage site=zesu_finish_final_pure ms=15000 ok=0 cpu_ms=15000
@@X begin final
@@X binders x
@@X counts props=3 small=2 kept=1
@@X stmt forall x : bv 64, bv_unsigned x < 2 ^ 64 ->
bv_unsigned x + 1 <= 2 ^ 64
@@X end
@@X skip final spatial
File "./Caller0300.v", line 33, characters 0-4:
Error:
 (in proof DesignedBoundary_800d5fb8): Attempt to save an incomplete proof

'''


def offset_after(text, needle):
    """Byte offset just past the line holding needle."""
    index = text.index(needle)
    return len(text[:text.index('\n', index) + 1].encode())


class Parsing(unittest.TestCase):
    def test_fields(self):
        fields = R.telemetry_fields('kind=lia stage=first_pass site="join entry" facts=-1 ms=4.5 ok=0 cpu_ms=4 extra')
        self.assertEqual(fields['kind'], 'lia')
        self.assertEqual(fields['site'], 'join entry')
        self.assertEqual(fields['args'], ['extra'])
        call = R.solver_call(fields)
        self.assertEqual(call['seconds'], 0.0045)
        self.assertEqual(call['cpu'], 0.004)
        self.assertIsNone(call['facts'])  # -1: not exactly one goal
        self.assertIs(call['ok'], False)
        self.assertEqual(R.telemetry_fields('lia x=1')['kind'], 'lia')

    def test_log(self):
        parsed = R.parse_log(LOG)
        self.assertEqual([R.command_class(c['command']) for c in parsed['commands']], ['imports', 'imports'])
        self.assertAlmostEqual(parsed['commands'][0]['seconds'], 1.5)
        self.assertEqual(len(parsed['zesu_runs']), 1)
        self.assertAlmostEqual(parsed['zesu_runs'][0]['seconds'], 10.5)
        self.assertEqual([r['site'] for r in parsed['stage_records']], ['zesu_run_pass', 'zesu_finish_final_pure'])
        self.assertEqual([c['kind'] for c in parsed['calls']], ['lia', 'bv_solve'])
        self.assertEqual(parsed['calls'][0]['end'], offset_after(LOG, 'kind=lia'))
        wrapped = parsed['calls'][1]  # the wrapped continuation line joins the record
        self.assertEqual(wrapped['site'], 'join entry')
        self.assertIs(wrapped['ok'], True)
        self.assertEqual((wrapped['rss_before_kib'], wrapped['rss_after_kib'], wrapped['start_t']), (1000, 3000, 1.0))
        self.assertEqual(wrapped['end'], offset_after(LOG, ' ok=1 cpu_ms=480'))
        self.assertEqual(parsed['events'], 4)
        final, skip = parsed['exports']
        self.assertEqual(final['statement'], 'forall x : bv 64, bv_unsigned x < 2 ^ 64 -> bv_unsigned x + 1 <= 2 ^ 64')
        self.assertEqual(final['class'], 'final <= bv_unsigned')
        self.assertEqual(final['counts'], {'props': '3', 'small': '2', 'kept': '1'})
        self.assertEqual(skip['class'], 'final skip: spatial')
        self.assertEqual(parsed['errors'][0]['line'], 33)
        self.assertIn('Attempt to save an incomplete proof', parsed['errors'][0]['text'])

    def test_leftovers_prefer_final(self):
        split = '@@X begin split\n@@X stmt 1 = 1\n@@X end\n'
        self.assertEqual([g['kind'] for g in R.leftovers(R.parse_log(split), closed=False)], ['split'])
        self.assertEqual(R.leftovers(R.parse_log(split), closed=True), [])
        both = split + '@@X begin final\n@@X stmt 2 = 2\n@@X end\n'
        self.assertEqual([g['kind'] for g in R.leftovers(R.parse_log(both), closed=False)], ['final'])

    def test_goal_class(self):
        self.assertEqual(R.goal_class('final', 'forall (a : Z) (b : Z), (a < b -> a = 0) -> f a = b'), 'final = f')
        self.assertEqual(R.goal_class('split', 'P x'), 'split prop P')
        exported = ('(forall (args : (@C.Args)), (forall (x13 : (@bv (64)%N)), ((@Coq.ZArith.BinInt.Z.le (0)%Z (x13)) '
                    '-> (@Coq.ZArith.BinInt.Z.le (@Coq.ZArith.BinInt.Z.add (x13) (8)%Z) (400)%Z))))')
        self.assertEqual(R.goal_class('final', exported), 'final <= add')
        self.assertEqual(R.goal_class('final', '(forall (a : (@T)), (@Coq.Init.Logic.eq (@list (@bv (8)%N)) a b))'),
                         'final = a')
        self.assertEqual(R.goal_class('final', '(forall (a : (@T)), (@Sealed.decodeItemCallDomain (@f a)))'),
                         'final prop decodeItemCallDomain')

    def test_command_classes(self):
        self.assertEqual(R.command_class('Qed.'), 'qed')
        self.assertEqual(R.command_class('Print~Assumptions~X.'), 'assumptions')
        self.assertEqual(R.command_class('zesu_block2.'), 'proof')
        self.assertEqual(R.command_class('Definition~X~:=~1.'), 'declarations')

    def test_instructions(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'perf.csv'
            path.write_text('# started on Mon\n\n12484250687,,instructions:u,597091858,100.00,,\n')
            self.assertEqual(R.instructions(path), 12484250687)
            path.write_text('<not counted>,,instructions:u,0,0,,\n')
            self.assertIsNone(R.instructions(path))
            self.assertIsNone(R.instructions(Path(temp) / 'none.csv'))

    def test_imports_regex(self):
        text = ('Require Import ZesuSsz.Generated.A.FP301.Pilot0300Entries.\n'
                'From Coq Require Import Lists.List ZArith.ZArith.\n'
                'Require Import isla.riscv64.riscv64.\n'
                'From ZesuSsz Require Import Contracts.ParentHeaderContract.\n')
        found = [(m.group(1), m.group(2)) for m in bench.IMPORT.finditer(text)]
        self.assertEqual(found, [(None, 'ZesuSsz.Generated.A.FP301.Pilot0300Entries'),
                                 ('Coq', 'Lists.List ZArith.ZArith'), (None, 'isla.riscv64.riscv64'),
                                 ('ZesuSsz', 'Contracts.ParentHeaderContract')])


def samples_for(text):
    """One sample per second; RSS grows by 1 GiB across the lia call and log bytes follow the text."""
    lia_end = offset_after(text, 'kind=lia')
    rows = []
    for second, (size, rss) in enumerate([(0, 1), (90, 1), (90, 1), (90, 1), (lia_end, 2), (lia_end, 2),
                                          (offset_after(text, 'kind=stage site=zesu_finish'), 2),
                                          (len(text.encode()), 3)]):
        rows.append({'t': 100.0 + second, 'rss_kib': rss * 2**20, 'hwm_kib': rss * 2**20, 'cpu_s': float(second * 10),
                     'log_bytes': size})
    return rows


class Joining(unittest.TestCase):
    def test_calls_and_stages(self):
        parsed = R.parse_log(LOG)
        timeline = R.Timeline(samples_for(LOG))
        R.join_calls(parsed['calls'], timeline)
        lia, bv = parsed['calls']
        self.assertEqual(lia['t'], 104.0)
        self.assertEqual(lia['rss_after_kib'], 2 * 2**20)
        self.assertEqual(lia['rss_before_kib'], 2**20)  # the row 4 s earlier
        self.assertEqual(lia['rss_growth_kib'], 2**20)
        self.assertEqual(bv['rss_growth_kib'], 2000)  # the telemetry's own rss0/rss1 win
        stages = R.stage_times(parsed, timeline, total_cpu=75.0)
        self.assertEqual(stages['zesu_run_pass'], {'cpu': 50.0, 'steps': 1, 'rss_growth_kib': None})
        self.assertEqual(stages['zesu_finish_final_pure']['cpu'], 15.0)
        self.assertEqual(R.stage_reached(parsed, 'NOT-CLOSED', 'failed'), 'imports (error)')
        killed = R.parse_log(LOG[:LOG.index('File ')])
        self.assertEqual(R.stage_reached(killed, 'NOT-CLOSED', 'cpu-cap'),
                         'zesu_finish_final_pure (1 zesu_run_pass, cpu-cap)')
        at_qed = R.parse_log(LOG.replace('File ', 'Chars 91 - 95 [Qed.] 0. secs (0.u,0.s)\nFile '))
        self.assertEqual(R.stage_reached(at_qed, 'NOT-CLOSED', 'failed'), 'qed (error)')

    def test_markers_with_samples(self):
        text = '@@S stage "a"\n@@S stage "b"\n'
        rows = [{'t': 1.0, 'rss_kib': 10, 'cpu_s': 1.0, 'log_bytes': 0},
                {'t': 2.0, 'rss_kib': 10, 'cpu_s': 2.0, 'log_bytes': 14},
                {'t': 3.0, 'rss_kib': 30, 'cpu_s': 7.0, 'log_bytes': 28}]
        stages = R.stage_times(R.parse_log(text), R.Timeline(rows), total_cpu=9.0)
        self.assertEqual(stages, {'a': {'cpu': 5.0, 'steps': 1, 'rss_growth_kib': 20},
                                  'b': {'cpu': 2.0, 'steps': 1, 'rss_growth_kib': 0}})

    def test_no_samples(self):
        parsed = R.parse_log(LOG)
        R.join_calls(parsed['calls'], R.Timeline([]))
        self.assertIsNone(parsed['calls'][0]['rss_growth_kib'])
        self.assertEqual(parsed['calls'][1]['rss_growth_kib'], 2000)
    def test_fallback_stages(self):
        text = ('Chars 0 - 10 [Require~Import~A.] 3. secs (3.u,0.s)\n'
                'Tactic call zesu_run ran for 20 secs (19.u,1.s) (success)\n'
                'Tactic call zesu_run ran for 0. secs (0.u,0.s) (failure after 1 backtracking)\n')
        parsed = R.parse_log(text)
        stages = R.stage_times(parsed, R.Timeline([]), total_cpu=100.0)
        self.assertEqual(stages['imports'], {'cpu': 3.0, 'steps': 1, 'rss_growth_kib': None})
        self.assertEqual(stages['proof.zesu_run'], {'cpu': 20.0, 'steps': 2, 'rss_growth_kib': None})
        self.assertEqual(stages['proof (unfinished)']['cpu'], 97.0)
        self.assertEqual(R.stage_reached(parsed, 'NOT-CLOSED', 'cpu-cap'), 'proof (2 zesu_runs, cpu-cap)')
        done = R.parse_log(text + 'Chars 11 - 20 [zesu_block2.] 30. secs (30.u,0.s)\n')
        self.assertEqual(R.stage_reached(done, 'NOT-CLOSED', 'failed'), 'qed')
        self.assertEqual(R.stage_reached(done, 'CLOSED', 'closed'), 'closed')


def write_block(directory, log, cpu, peak_gib, verdict, returncode=1, samples=None, instructions=None):
    directory.mkdir(parents=True)
    (directory / 'measure.json.log').write_text(log)
    (directory / 'measure.json').write_text(json.dumps({
        'schema': 'measure/1', 'started_utc': 'x', 'returncode': returncode, 'cpu_user': cpu, 'cpu_sys': 0.0,
        'max_rss_kib': int(peak_gib * 2**20), 'wall': cpu + 1}))
    record = {'verdict': verdict, 'case': directory.name}
    if verdict != 'CLOSED':
        record['reason'] = 'coqc exit %d' % returncode
    (directory / ('CLOSURE.json' if verdict == 'CLOSED' else 'NOT-CLOSED.json')).write_text(json.dumps(record))
    (directory / 'run.log').write_text('')
    if samples:
        (directory / 'samples.jsonl').write_text(''.join(json.dumps(row) + '\n' for row in samples) + '{"t": 1')
    if instructions:
        (directory / 'perf.csv').write_text('%d,,instructions:u,1,100.00,,\n' % instructions)


def write_run(root, name, blocks):
    run = root / name
    run.mkdir()
    members = [{'function': 'decodeParentHeader', 'callers': 'c', 'case': '0300'},
               {'function': 'decodeItem', 'callers': 'c', 'case': '0164', 'label': '6ac4'},
               {'function': 'nextUint64', 'callers': 'c', 'case': '0064'}]
    (run / 'RUN.json').write_text(json.dumps({
        'set': 'BENCH-T', 'head': 'a' * 40, 'rules': None, 'bench_head': 'b' * 40, 'bank': '/bank',
        'telemetry': True, 'caps': {'cpu_seconds': 3600, 'limit_gib': 24}, 'members': members}))
    rows = []
    for member, spec in zip(members, blocks):
        if spec is None:
            continue
        directory = run / 'runs' / member['case']
        write_block(directory, **spec)
        rows.append({'key': R.member_key(member), 'dir': str(directory)})
    (run / 'results.jsonl').write_text(''.join(json.dumps(row) + '\n' for row in rows))
    return run


class Report(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        closed = 'Chars 0 - 5 [zesu_block2.] 50. secs (50.u,0.s)\nChars 6 - 9 [Qed.] 5. secs (5.u,0.s)\n'
        self.base = write_run(self.root, 'base', [
            dict(log=LOG, cpu=100.0, peak_gib=4.0, verdict='NOT-CLOSED', samples=samples_for(LOG), instructions=2 * 10**12),
            dict(log=closed, cpu=60.0, peak_gib=9.0, verdict='CLOSED', returncode=0, instructions=10**12),
            None])
        self.new = write_run(self.root, 'new', [
            dict(log=LOG, cpu=3600.0, peak_gib=6.0, verdict='NOT-CLOSED', returncode=-9, samples=samples_for(LOG)),
            dict(log=closed, cpu=54.0, peak_gib=8.5, verdict='CLOSED', returncode=0, instructions=9 * 10**11),
            dict(log='', cpu=1.0, peak_gib=0.1, verdict='NOT-CLOSED')])

    def test_block(self):
        run = R.load_run(self.base)
        block = run['blocks'][0]['block']
        self.assertEqual(block['verdict'], 'NOT-CLOSED')
        self.assertEqual(block['end'], 'failed')
        self.assertEqual(block['instructions'], 2 * 10**12)
        self.assertEqual(block['peak_gib'], 4.0)
        self.assertEqual(block['samples'], 8)  # the partial last sampler line is skipped
        self.assertEqual(R.leftover_classes(block), {'final <= bv_unsigned': 1, 'final skip: spatial': 1})
        self.assertEqual(block['leftovers'][0]['statement'][:6], 'forall')
        self.assertIsNone(run['blocks'][2]['block'])
        self.assertEqual(R.load_run(self.new)['blocks'][0]['block']['end'], 'cpu-cap')

    def test_ranking(self):
        rank = R.ranking(R.load_run(self.base))
        self.assertEqual(rank['kind'][0]['name'], 'lia')
        self.assertEqual(rank['kind'][0]['failed'], 1)
        self.assertEqual(rank['kind'][0]['rss_growth_kib'], 2**20)
        self.assertEqual(rank['site'][0]['name'], 'premise @ zesu_run_pass')
        names = [row['name'] for row in rank['stage']]
        self.assertEqual(names[0], 'zesu_run_pass')
        self.assertIn('proof', names)  # the closed block's fallback stages
        self.assertEqual(rank['caller'], [])  # no caller-mode records

    def test_caller_ranking(self):
        log = ('@@T kind=bv_solve site=bv_solve stage=zesu_run_pass facts=3 nodes=40 goal_nodes=9 ms=900 ok=0 '
               'cpu_ms=900 caller=bv_solve@automation:1668>liStep@Hooks:10>zesu_run_pass_v1@Finish:9 shape=eq:bv\n'
               '@@T kind=bv_solve site=bv_solve stage=zesu_run_pass facts=3 nodes=40 goal_nodes=9 ms=100 ok=1 '
               'cpu_ms=100 caller=bv_solve@automation:1668>liStep@Hooks:10 shape=eq:bv\n')
        run = write_run(self.root, 'callers', [dict(log=log, cpu=10.0, peak_gib=1.0, verdict='NOT-CLOSED'), None, None])
        rank = R.ranking(R.load_run(run))
        self.assertEqual([(row['name'], row['calls'], row['cpu']) for row in rank['caller']],
                         [('bv_solve @ zesu_run_pass <- bv_solve@automation:1668>liStep@Hooks:10 [eq:bv]', 1, 0.9)])
        self.assertIn('failing calls by site @ stage <- caller [goal shape]', R.render(R.load_run(run)))

    def test_render_with_base(self):
        text = R.render(R.load_run(self.new), R.load_run(self.base))
        self.assertIn('### decodeItem 0164 (6ac4)', text)
        self.assertIn('closed 1 of 3 (ran 3)', text)
        self.assertIn('base base: closed 1', text)
        self.assertIn('| base: CLOSED | closed | 60.0 (-10.0%) | 1000.0 (-10.0%) | 9.00 (-0.50) |', text)
        self.assertIn('top 5 by time:', text)
        self.assertIn('| lia | zesu_run_pass | premise | 417 | 66500 | 12 | 3.90 | no | 1.00 |', text)
        self.assertIn('top 5 by RSS growth:', text)
        self.assertIn('leftover goal classes: final <= bv_unsigned x1, final skip: spatial x1', text)
        self.assertIn('## Ranking across the set', text)
        self.assertIn('verdict changes: none', text)

    def test_report_command_writes_files(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            self.assertEqual(bench.main(['report', str(self.new), '--base', str(self.base)]), 0)
        self.assertTrue((self.new / 'REPORT-vs-base.md').is_file())
        data = json.loads((self.new / 'REPORT-vs-base.json').read_text())
        self.assertEqual(data['summary']['closed'], 1)
        self.assertEqual(data['blocks'][0]['block']['leftovers'], {'final <= bv_unsigned': 1, 'final skip: spatial': 1})
        self.assertIn('# BENCH-T run new', output.getvalue())

    def test_error_class_without_telemetry(self):
        text = ('File "./Caller0000.v", line 33, characters 0-4:\nError:\n'
                ' (in proof DesignedBoundary_800d5cb8): Attempt to save an incomplete proof\n')
        directory = self.root / 'plain'
        write_block(directory, log=text, cpu=10.0, peak_gib=1.0, verdict='NOT-CLOSED')
        block = R.load_block(directory)
        self.assertEqual(R.leftover_classes(block), {'(no export) Attempt to save an incomplete proof': 1})


class SetDefinition(unittest.TestCase):
    def test_bench_v1(self):
        data = bench.load_set('BENCH-v1')
        cases = [(member['function'], member['case']) for member in data['members']]
        self.assertEqual(len(cases), len(set(cases)))
        self.assertEqual(data['caps'], {'cpu_seconds': 3600, 'limit_gib': 24})
        counts = {}
        for function, _ in cases:
            counts[function] = counts.get(function, 0) + 1
        self.assertEqual(counts, {'decodeParentHeader': 9, 'decodeItem': 3, 'nextUint64': 2, 'berlinGasCalc': 2})
        for member in data['members']:
            self.assertLessEqual(member['claim_gib'], data['caps']['limit_gib'])
            self.assertTrue(member['why'])
        overlay_functions = {overlay['name'] for overlay in data['overlays']}
        self.assertEqual(overlay_functions, {'berlinGasCalc'})


if __name__ == '__main__':
    unittest.main()
