"""Exercise the stock shell transaction with a temporary kernel inventory."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class UnifiedGuardRoute(unittest.TestCase):
    def test_request_path_contains_a_fresh_generation_without_reserving(self):
        root=Path(__file__).resolve().parents[3]
        with tempfile.TemporaryDirectory() as temporary:
            directory=Path(temporary)
            environment={k:v for k,v in os.environ.items() if not k.startswith('ZESU_')}
            environment.update(ZESU_GUARD_STATE=str(directory),ZESU_GATE_LOCK=str(directory/'gate.lock'))
            library=(root/'tools/resource_guard.sh').read_text().split('\nprune_scope_registry\n',1)[0]
            result=subprocess.run(['bash'],input=library+'\nreserve_coqc $$\nreserve_coqc $$\n',
                                  env=environment,text=True,capture_output=True,timeout=10)
            self.assertEqual(result.returncode,0,result.stderr)
            paths=result.stdout.splitlines()
            self.assertEqual(len(paths),2)
            self.assertNotEqual(paths[0],paths[1])
            failure=subprocess.run(['bash'],input=library+'\ncat() { return 1; }\nreserve_coqc $$\n',
                                   env=environment,text=True,capture_output=True,timeout=10)
            self.assertEqual(failure.returncode,2)
            self.assertEqual(failure.stdout,'')
            for path in paths:
                self.assertRegex(Path(path).name,r'^[0-9]+\.[0-9a-f]{8}-(?:[0-9a-f]{4}-){3}[0-9a-f]{12}$')
                self.assertFalse(Path(path).exists())

    def test_dead_marker_reader_retains_unknown_memory_evidence(self):
        root=Path(__file__).resolve().parents[3]
        with tempfile.TemporaryDirectory() as temporary:
            directory=Path(temporary)
            tokens=directory/'coqc-reservations';tokens.mkdir()
            marker=tokens/'2147483647.legacy'
            marker.write_text('confirmed\nwriter=\naggregate=\nmemory_fence_bytes=68719476736\n')
            original=marker.read_bytes()
            environment={k:v for k,v in os.environ.items() if not k.startswith('ZESU_')}
            environment.update(ZESU_GUARD_STATE=str(directory),ZESU_GATE_LOCK=str(directory/'gate.lock'))
            library=(root/'tools/resource_guard.sh').read_text().split('\nprune_scope_registry\n',1)[0]
            result=subprocess.run(['bash'],input=library+'\nlive_reservations\n',env=environment,
                                  text=True,capture_output=True,timeout=10)
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(result.stdout,'')
            self.assertEqual(marker.read_bytes(),original)

    def test_status_four_never_authorizes_either_release_to_remove_a_token(self):
        root=Path(__file__).resolve().parents[3]
        for command in ('release_coqc "$marker"','release_aggregate_reservations fixture.slice'):
            with self.subTest(command=command),tempfile.TemporaryDirectory() as temporary:
                directory=Path(temporary);tokens=directory/'coqc-reservations';tokens.mkdir()
                marker=tokens/'2147483647.legacy'
                marker.write_text('confirmed\nwriter=\naggregate=fixture.slice\n')
                original=marker.read_bytes()
                helper=directory/'memory.py';helper.write_text('raise SystemExit(4)\n')
                environment={k:v for k,v in os.environ.items() if not k.startswith('ZESU_')}
                environment.update(ZESU_GUARD_STATE=str(directory),ZESU_GATE_LOCK=str(directory/'gate.lock'),
                                   ZESU_MODULE_MEMORY_TOOL=str(helper))
                library=(root/'tools/resource_guard.sh').read_text().split('\nprune_scope_registry\n',1)[0]
                script='\nmarker="$COQC_RESERVATIONS/2147483647.legacy"\n'+command+'\n'
                result=subprocess.run(['bash'],input=library+script,env=environment,
                                      text=True,capture_output=True,timeout=10)
                self.assertEqual(result.returncode,4,result.stderr)
                self.assertEqual(marker.read_bytes(),original)

    def test_confirm_and_release_hold_guard_lock_before_ledger_lock(self):
        root=Path(__file__).resolve().parents[3]
        with tempfile.TemporaryDirectory() as temporary:
            directory=Path(temporary)
            ledger=directory/'LEDGER.json'
            ledger.write_text(json.dumps({'fixed_claims':{},'shell_marker_directory':str(directory/'coqc-reservations')}))
            wrapper=directory/'memory.py'
            wrapper.write_text('''import argparse,fcntl,json,os,sys
from pathlib import Path
sys.path.insert(0,os.environ['FIXTURE_CODE'])
import admission_memory as M
p=argparse.ArgumentParser();p.add_argument('command');p.add_argument('--marker',type=Path,required=True)
p.add_argument('--replacement',type=Path);p.add_argument('--request-bytes',type=int);p.add_argument('--available-bytes',type=int)
a=p.parse_args();root=Path(os.environ['ZESU_GUARD_STATE'])
with Path(os.environ['ZESU_GATE_LOCK']+'.mutex').open('a') as lock:
 try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 except BlockingIOError:pass
 else:raise AssertionError('The shell released GATE_MUTEX before its ledger transaction.')
reader=M.ScopeReader(proc=root/'proc',cgroup_root=root/'cgroup')
parent=reader.parent;parent.mkdir(parents=True,exist_ok=True)
(parent/'memory.max').write_text(str(M.SLICE_MAX_BYTES));(parent/'memory.swap.max').write_text('0')
pid=int(a.marker.name.split('.')[0]);raw=Path('/proc')/str(pid)/'stat'
ticks=int(raw.read_text().rsplit(')',1)[1].split()[19])
group=parent/f'zesuworkloads-aggregate{os.getuid()}p{pid}r1.slice';group.mkdir(exist_ok=True)
(group/'memory.current').write_text('1024');(group/'cgroup.events').write_text('populated 1\\n')
actor=reader.proc/str(pid);actor.mkdir(parents=True,exist_ok=True)
(actor/'stat').write_text(f'{pid} (fixture) '+' '.join(['S','1']+['0']*17+[str(ticks)]))
(actor/'cgroup').write_text('0::/'+str(group.relative_to(reader.root))+'\\n')
if a.command=='ledger-confirm':
 text=a.replacement.read_text().replace('aggregate=\\n','aggregate='+group.name+'\\n')
 a.replacement.write_text(text)
 result=M.confirm_shell(a.marker,a.replacement,a.request_bytes,a.available_bytes,reader=reader)
 raise SystemExit(0 if result['fits'] else 3)
if a.command=='ledger-release':
 (group/'cgroup.events').write_text('populated 0\\n')
 raise SystemExit(0 if M.release_shell(a.marker,reader=reader) else 4)
raise AssertionError('Unexpected fixture operation.')
''')
            environment={k:v for k,v in os.environ.items() if not k.startswith('ZESU_')}
            environment.update(ZESU_GUARD_STATE=str(directory),ZESU_GATE_LOCK=str(directory/'gate.lock'),
                               ZESU_CANONICAL_LEDGER=str(ledger),ZESU_MODULE_MEMORY_TOOL=str(wrapper),
                               FIXTURE_CODE=str(root/'tools/block/harness/code'))
            library=(root/'tools/resource_guard.sh').read_text().split('\nprune_scope_registry\n',1)[0]
            script='''
cache_disk_admission() { :; }
hold_reason() { :; }
compiler_admission_reason() { :; }
memory() { echo $((256*GIB)) 0 $((200*GIB)); }
marker=$(reserve_coqc $$) || exit 11
confirm_coqc "$marker" || exit 12
[ -f "$marker" ] || exit 13
release_coqc "$marker" || exit 14
[ ! -e "$marker" ] || exit 15
'''
            result=subprocess.run(['bash','-c',library+script,str(root/'tools/resource_guard.sh')],env=environment,text=True,
                                  capture_output=True,timeout=15)
            self.assertEqual(result.returncode,0,result.stderr)
            data=json.loads(ledger.read_text())
            self.assertEqual(list(data['fixed_claims'].values()),[0])
            self.assertEqual(len(data['shell_claim_owners']),1)
            self.assertEqual(len(data['shell_releases']),1)


if __name__=='__main__':unittest.main()
