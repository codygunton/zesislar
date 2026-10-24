"""Exercise Dune compiler admission with a fake compiler and private guard state."""

import json
import os
import shutil
import signal
import subprocess
import sys
import time
import unittest
from pathlib import Path

import test_guard
from coqc_recipe import compiler_recipe


TOOLS = Path(__file__).resolve().parent


class GateQueueTest(unittest.TestCase):
    def setUp(self):
        self.fixture = test_guard.GuardLockTest()
        self.fixture.setUp()
        self.addCleanup(self.fixture.tearDown)
        self.root = Path(self.fixture.directory.name)
        self.environment = self.fixture.environment.copy()
        self.environment["ZESU_GUARD_POLL"] = "0.02"
        self.waiters = Path(str(self.fixture.lock) + ".waiters")
        self.events = self.root / "gate-events.jsonl"
        self.job = self.root / "job.py"
        self.job.write_text(
            "import json,os,pathlib,sys,time\n"
            "name,events,release=sys.argv[1:]\n"
            "active=pathlib.Path(events+'.active')\n"
            "fd=os.open(active,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600);os.close(fd)\n"
            "fd=os.open(events,os.O_WRONLY|os.O_CREAT|os.O_APPEND,0o600)\n"
            "os.write(fd,(json.dumps({'name':name,'pid':os.getpid()})+'\\n').encode());os.close(fd)\n"
            "while not pathlib.Path(release).exists():time.sleep(0.01)\n"
            "active.unlink()\n")
        self.processes = []
        self.addCleanup(self.stop_processes)

    def stop_processes(self):
        for process in self.processes:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGTERM)
            process.communicate(timeout=5)

    def wait_for(self, predicate):
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            if predicate():
                return
            time.sleep(0.01)
        self.fail("The gate fixture did not reach its expected state.")

    def records(self):
        return [json.loads(line) for line in self.events.read_text().splitlines()] \
            if self.events.exists() else []

    def waiter_records(self):
        records = []
        for path in self.waiters.glob("*.waiter"):
            try:
                records.append((path, path.read_text().split()))
            except FileNotFoundError:
                continue
        return records

    def start(self, name, gate_class):
        environment = {**self.environment, "ZESU_GATE_CLASS": gate_class}
        process = subprocess.Popen(
            [str(test_guard.GUARD), "locked", name, "--", sys.executable,
             str(self.job), name, str(self.events), str(self.root / (name + ".release"))],
            env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, start_new_session=True)
        self.processes.append(process)
        return process

    def queued(self, process):
        self.wait_for(lambda: any(row[2] == str(process.pid)
                                 for _, row in self.waiter_records()))

    def started(self, name):
        self.wait_for(lambda: any(row["name"] == name for row in self.records()))

    def finish(self, process, name):
        (self.root / (name + ".release")).touch()
        _, stderr = process.communicate(timeout=5)
        self.assertEqual(process.returncode, 0, stderr)

    def assert_clean(self):
        self.assertFalse(self.fixture.lock.exists())
        self.assertEqual(self.waiter_records(), [])
        self.assertFalse(Path(str(self.events) + ".active").exists())

    def test_priority_and_fifo_preserve_the_running_gate(self):
        holder = self.start("holder", "preview")
        self.started("holder")
        original = self.fixture.lock.read_bytes()
        arrivals = [("preview", "preview"), ("child1", "child"),
                    ("root1", "root"), ("child2", "child"), ("root2", "root")]
        processes = {}
        for name, gate_class in arrivals:
            processes[name] = self.start(name, gate_class)
            self.queued(processes[name])
            self.assertEqual(self.fixture.lock.read_bytes(), original)
            self.assertIsNone(holder.poll())
            self.assertEqual([r["name"] for r in self.records()], ["holder"])
        self.finish(holder, "holder")
        order = ["root1", "root2", "child1", "child2", "preview"]
        for name in order:
            self.started(name)
            self.finish(processes[name], name)
        self.assertEqual([r["name"] for r in self.records()], ["holder", *order])
        self.assert_clean()
        print("FAIR_LANE_COMPARISON", json.dumps({
            "arrivals": [name for name, _ in arrivals], "execution": order,
            "running_holder_unchanged": True, "waiters_removed": True}))

    def test_later_root_does_not_interrupt_a_running_preview(self):
        preview = self.start("preview", "preview")
        self.started("preview")
        original = self.fixture.lock.read_bytes()
        root = self.start("root", "root")
        self.queued(root)
        self.assertEqual(self.fixture.lock.read_bytes(), original)
        self.assertIsNone(preview.poll())
        self.assertEqual(len(self.records()), 1)
        self.finish(preview, "preview")
        self.started("root")
        self.finish(root, "root")
        self.assert_clean()

    def test_legacy_busy_call_refuses_and_removes_its_registration(self):
        holder = self.start("holder", "child")
        self.started("holder")
        result = self.fixture.guard("locked", "legacy", "--", "true")
        self.assertEqual(result.returncode, 3, result.stderr)
        self.assertEqual(self.waiter_records(), [])
        self.assertIsNone(holder.poll())
        self.finish(holder, "holder")
        result = self.fixture.guard("locked", "legacy", "--", "true")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_clean()

    def test_cancelled_waiter_does_not_block_a_preview(self):
        holder = self.start("holder", "child")
        self.started("holder")
        root = self.start("root", "root")
        self.queued(root)
        root.terminate()
        root.communicate(timeout=5)
        self.wait_for(lambda: not self.waiter_records())
        preview = self.start("preview", "preview")
        self.queued(preview)
        self.finish(holder, "holder")
        self.started("preview")
        self.finish(preview, "preview")
        self.assertEqual([r["name"] for r in self.records()], ["holder", "preview"])
        self.assert_clean()

    def test_dead_reused_and_invalid_waiters_are_removed(self):
        self.waiters.mkdir()
        start = Path(f"/proc/{os.getpid()}/stat").read_text().rsplit(") ", 1)[1].split()[19]
        # A live PID with a wrong start tick represents PID reuse.
        for name, record in {
            "dead": "root 1 999999999 1 999999998 1 999999997 1\n",
            "reused-owner": f"root 2 {os.getpid()} 0 {os.getpid()} {start} {os.getpid()} {start}\n",
            "reused-waiter": f"root 3 {os.getpid()} {start} {os.getpid()} 0 {os.getpid()} {start}\n",
            "reused-caller": f"root 4 {os.getpid()} {start} {os.getpid()} {start} {os.getpid()} 0\n",
            "malformed": "preview invalid\n",
        }.items():
            (self.waiters / (name + ".waiter")).write_text(record)
        result = self.fixture.guard("lock-status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.waiter_records(), [])
        preview = self.start("preview", "preview")
        self.started("preview")
        self.finish(preview, "preview")
        self.assert_clean()

    def test_external_owner_and_waiter_lifetimes_are_both_required(self):
        holder = self.start("holder", "child")
        self.started("holder")
        owner = subprocess.Popen(["sleep", "30"])
        self.addCleanup(lambda: owner.poll() is None and owner.terminate())
        caller = subprocess.Popen(
            [str(test_guard.GUARD), "lock-want", str(owner.pid), "external"],
            env={**self.environment, "ZESU_GATE_CLASS": "root"},
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            start_new_session=True)
        self.processes.append(caller)
        self.wait_for(lambda: any(row[2] == str(owner.pid)
                                 for _, row in self.waiter_records()))
        caller.terminate()
        caller.communicate(timeout=5)
        self.wait_for(lambda: not self.waiter_records())
        self.assertIsNone(owner.poll())
        owner.terminate()
        owner.wait(timeout=5)
        self.finish(holder, "holder")
        self.assert_clean()

    def test_dead_external_owner_cannot_acquire_through_a_live_caller(self):
        holder = self.start("holder", "child")
        self.started("holder")
        owner = subprocess.Popen(["sleep", "30"])
        try:
            caller = subprocess.Popen(
                [str(test_guard.GUARD), "lock-want", str(owner.pid), "external"],
                env={**self.environment, "ZESU_GATE_CLASS": "root"},
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                start_new_session=True)
            self.processes.append(caller)
            self.wait_for(lambda: any(row[2] == str(owner.pid)
                                     for _, row in self.waiter_records()))
            owner.terminate()
            owner.wait(timeout=5)
            caller.communicate(timeout=5)
            self.assertEqual(caller.returncode, 2)
            self.assertEqual(self.waiter_records(), [])
            self.assertIsNone(holder.poll())
        finally:
            if owner.poll() is None:
                owner.terminate()
                owner.wait(timeout=5)
        self.finish(holder, "holder")
        self.assert_clean()

    def test_killed_waiter_is_removed_by_the_next_lock_check(self):
        holder = self.start("holder", "preview")
        self.started("holder")
        root = self.start("root", "root")
        self.queued(root)
        os.killpg(root.pid, signal.SIGKILL)
        root.communicate(timeout=5)
        self.fixture.guard("lock-status")
        self.assertEqual(self.waiter_records(), [])
        self.assertIsNone(holder.poll())
        self.finish(holder, "holder")
        self.assert_clean()

    def test_killed_acquisition_subshell_is_stale_with_live_owner_and_caller(self):
        holder = self.start("holder", "child")
        self.started("holder")
        caller = subprocess.Popen(
            [str(test_guard.GUARD), "lock-want", str(os.getpid()), "external"],
            env={**self.environment, "ZESU_GATE_CLASS": "root"},
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            start_new_session=True)
        self.processes.append(caller)
        self.wait_for(lambda: any(row[2] == str(os.getpid())
                                 for _, row in self.waiter_records()))
        record = self.waiter_records()[0][1]
        waiter = int(record[4])
        self.assertNotEqual(waiter, caller.pid)
        self.assertEqual(int(record[6]), caller.pid)
        os.kill(caller.pid, signal.SIGSTOP)
        try:
            os.kill(waiter, signal.SIGKILL)
            self.wait_for(lambda: not Path(f"/proc/{waiter}/stat").exists() or
                          Path(f"/proc/{waiter}/stat").read_text().rsplit(") ", 1)[1].split()[0] == "Z")
            self.fixture.guard("lock-status")
            self.assertEqual(self.waiter_records(), [])
            self.assertIsNone(caller.poll())
            self.assertIsNone(holder.poll())
        finally:
            os.kill(caller.pid, signal.SIGCONT)
            caller.communicate(timeout=5)
        self.finish(holder, "holder")
        self.assert_clean()

    def test_concurrent_child_arrivals_use_unique_fifo_tickets_and_one_owner(self):
        holder = self.start("holder", "child")
        self.started("holder")
        processes = {f"child{i}": self.start(f"child{i}", "child") for i in range(6)}
        self.wait_for(lambda: len(self.waiter_records()) == len(processes))
        names = {process.pid: name for name, process in processes.items()}
        tickets = [(int(row[1]), names[int(row[2])]) for _, row in self.waiter_records()]
        self.assertEqual(len({ticket for ticket, _ in tickets}), len(processes))
        order = [name for _, name in sorted(tickets)]
        self.assertEqual([r["name"] for r in self.records()], ["holder"])
        self.finish(holder, "holder")
        for i, name in enumerate(order):
            self.started(name)
            self.assertEqual([r["name"] for r in self.records()], ["holder", *order[:i + 1]])
            self.finish(processes[name], name)
        self.assert_clean()

    def test_reused_owner_lock_is_removed_without_signalling_the_pid(self):
        self.fixture.lock.write_text(f"state=held holder=stale pid={os.getpid()} pid_start=0\n")
        result = self.fixture.guard("lock-status")
        self.assertIn("stale gate lock removed", result.stderr)
        self.assert_clean()

    def test_wanted_lock_is_not_replaced_by_a_higher_class(self):
        owner = subprocess.Popen(["sleep", "30"])
        try:
            result = subprocess.run(
                [str(test_guard.GUARD), "lock-want", str(owner.pid), "preview"],
                env={**self.environment, "ZESU_GATE_CLASS": "preview"},
                capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 0, result.stderr)
            original = self.fixture.lock.read_bytes()
            self.assertTrue(original.startswith(b"state=wanted "))
            root = self.start("root", "root")
            self.queued(root)
            self.assertEqual(self.fixture.lock.read_bytes(), original)
            self.assertIsNone(owner.poll())
            self.assertEqual(self.records(), [])
            self.fixture.guard("lock-release", str(owner.pid))
            self.started("root")
            self.finish(root, "root")
        finally:
            owner.terminate()
            owner.wait(timeout=5)
        self.assert_clean()

    def test_invalid_class_and_dead_owner_do_not_register(self):
        for arguments, environment in [
            (["locked", "invalid", "--", "true"], {"ZESU_GATE_CLASS": "invalid"}),
            (["lock-want", "999999999", "dead"], {"ZESU_GATE_CLASS": "root"}),
        ]:
            result = subprocess.run([str(test_guard.GUARD), *arguments],
                                    env={**self.environment, **environment},
                                    capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 2, result.stderr)
            self.assert_clean()


class DuneCompilerGuardTest(unittest.TestCase):
    def setUp(self):
        self.fixture = test_guard.GuardLockTest()
        self.fixture.setUp()
        self.addCleanup(self.fixture.tearDown)
        self.root = Path(self.fixture.directory.name)
        self.blocked = self.fixture.prepare_blocked_fixture(16)
        self.environment = self.fixture.environment.copy()
        self.environment.pop("ZESU_COQC_RESERVATION", None)
        self.environment.pop("ZESU_COQC_SCOPE", None)
        tools = self.root / "tools"
        (tools / "guard-bin").mkdir(parents=True)
        (tools / "det").mkdir()
        for name in ("resource_guard.sh", "dune_coqc_guarded.sh", "coqc_scratch.sh",
                     "coqc_recipe.py", "coqc_findlib.py", "module_memory.py",
                     "det/coqc_slots.py", "guard-bin/dune"):
            shutil.copy2(TOOLS / name, tools / name)
        self.wrapper = tools / "guard-bin/coqc"
        shutil.copy2(TOOLS / "dune_coqc_guarded.sh", self.wrapper)
        prefix = self.root / "switch/_opam"
        (prefix / "bin").mkdir(parents=True)
        self.events = self.root / "compiler-events.jsonl"
        compiler = prefix / "bin/coqc"
        compiler.write_text(
            "#!/usr/bin/env python3\n"
            "import json,os,pathlib,resource,sys\n"
            "args=sys.argv[1:]\n"
            "if args and args[0]=='--print-version': print('8.19.2 4.14.4');sys.exit(0)\n"
            "if args==['--config']:\n"
            " print('COQLIB='+os.environ['FAKE_COQLIB']);sys.exit(0)\n"
            "source=next((pathlib.Path(x) for x in args if x.endswith('.v')),None)\n"
            "if source is None: sys.exit(0)\n"
            "fd=os.open(os.environ['FAKE_COMPILER_EVENTS'],os.O_WRONLY|os.O_CREAT|os.O_APPEND,0o600)\n"
            "os.write(fd,(json.dumps({'source':str(source),'args':args,'OCAMLPATH':os.environ.get('OCAMLPATH'),'token':os.environ.get('ZESU_COQC_RESERVATION'),'scope':os.environ.get('ZESU_COQC_SCOPE'),'slots':len(list(pathlib.Path(os.environ['ZESU_GUARD_STATE'],'coqc-reservations').iterdir())),'cpu':resource.getrlimit(resource.RLIMIT_CPU)[0],'memory':os.environ.get('ZESU_MODULE_LIMIT_GIB')})+'\\n').encode());os.close(fd)\n"
            "for suffix in ['.vo','.glob','.vos','.vok']: source.with_suffix(suffix).write_text('fixture')\n"
            "if os.environ.get('FAKE_BLOCK_AFTER_FIRST')=='1' and source.stem=='First':\n"
            " pathlib.Path(os.environ['GUARD_TEST_BLOCKED_COUNT']).write_text('17\\n')\n")
        compiler.chmod(0o755)
        self.environment.update(OPAM_SWITCH_PREFIX=str(prefix),
                                FAKE_COMPILER_EVENTS=str(self.events),
                                FAKE_COQLIB=str(self.root / "coqlib"))
        (self.root / "coqlib").mkdir()
        self.scope_log = self.root / "compiler-scopes.jsonl"
        self.environment["FAKE_SCOPE_LOG"] = str(self.scope_log)
        (self.fixture.bin / "systemd-run").write_text(
            '#!/usr/bin/env python3\n'
            'import json,os,sys\n'
            'with open(os.environ["FAKE_SCOPE_LOG"],"a") as f: f.write(json.dumps(sys.argv[1:])+"\\n")\n'
            'args=sys.argv[sys.argv.index("--")+1:];os.execvp(args[0],args)\n')


    def compiler_events(self):
        return [json.loads(line) for line in self.events.read_text().splitlines()] \
            if self.events.exists() else []

    def test_dune_wrapper_propagates_the_configured_gate_fence(self):
        self.prepare_recordless_private_build()
        source = self.root / "Configured.v"
        source.write_text("(* Fake compiler input. *)\n")
        for limit in (None, "6", "16", "32"):
            with self.subTest(limit=limit):
                environment = {**self.environment, "ZESU_MODULE_LIMIT_GIB": "99"}
                if limit is not None:
                    environment["ZESU_GATE_MODULE_LIMIT_GIB"] = limit
                result = subprocess.run([str(self.wrapper), str(source)],
                                        cwd=self.root, env=environment,
                                        capture_output=True, text=True, timeout=5)
                self.assertEqual(result.returncode, 0, result.stderr)
                memory = limit or McpThresholdTest.guard_default_memory()
                self.assertEqual(self.compiler_events()[-1]["memory"], memory)
                scopes = [json.loads(line) for line in self.scope_log.read_text().splitlines()]
                self.assertIn(f"MemoryMax={memory}G", scopes[-1])
                self.assertIn("MemorySwapMax=0", scopes[-1])

    def test_dune_wrapper_rejects_invalid_gate_fences_before_admission(self):
        for limit in ("", "5", "33", "64", "-6", "6.5", "invalid"):
            with self.subTest(limit=limit):
                environment = {**self.environment, "ZESU_GATE_MODULE_LIMIT_GIB": limit}
                result = subprocess.run([str(self.wrapper), "Fixture.v"],
                                        cwd=self.root, env=environment,
                                        capture_output=True, text=True, timeout=5)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("integer from 6 through 32", result.stderr)
                self.assertEqual(self.compiler_events(), [])
                self.assertFalse(self.scope_log.exists())

    def prepare_recordless_private_build(self):
        (self.root / "dune-project").write_text("(lang dune 3.17)\n")
        private = self.root / "_build/agents/private"
        (private / "default").mkdir(parents=True)
        (self.root / "_build/default").symlink_to(private / "default")
        self.assertFalse((private / "coqc-ocamlpath.json").exists())

    def test_failed_snapshot_prevents_every_compiler_route(self):
        self.prepare_recordless_private_build()
        source = self.root / "Probe.v"
        source.write_text("(* Fake compiler input. *)\n")
        build = self.root / "build"
        build.mkdir()
        (build / "trace.csexp").write_bytes(b"")
        compiler = Path(self.environment["OPAM_SWITCH_PREFIX"]) / "bin/coqc"
        (build / "coqc_recipe.json").write_text(json.dumps({
            "command": [str(compiler), "Original.v"], "working_dir": str(self.root)}))
        shutil.copy2(TOOLS / "rocq_coqc_guarded.sh", self.root / "tools/rocq_coqc_guarded.sh")
        scratch = [str(self.root / "tools/coqc_scratch.sh"), str(source), str(build)]
        guard = self.root / "tools/resource_guard.sh"
        routes = ([str(self.wrapper), str(source)],
                  [str(self.root / "tools/dune_coqc_guarded.sh"), str(source)],
                  scratch, [str(guard), "scope", "outer", "--", *scratch],
                  [str(self.root / "tools/rocq_coqc_guarded.sh"), str(source)])
        for status in (2, 3):
            (self.fixture.bin / "pgrep").write_text(f"#!/bin/sh\nexit {status}\n")
            for ambient in (None, str(self.root / "ambient/lib")):
                environment = dict(self.environment)
                environment.pop("OCAMLPATH", None)
                if ambient is not None:
                    environment["OCAMLPATH"] = ambient
                for route in routes:
                    with self.subTest(status=status, ambient=ambient, route=route):
                        result = subprocess.run(route, cwd=self.root, env=environment,
                                                capture_output=True, text=True, timeout=5)
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn("compiler snapshot failed", result.stderr)
                        self.assertEqual(self.compiler_events(), [])
                        self.assertFalse(self.scope_log.exists())
                        reservations = Path(environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
                        self.assertEqual(list(reservations.iterdir()), [])

    def test_actual_coqc_wrapper_tree_counts_once_with_16_writer_slots(self):
        # sleep is an ELF executable. Renaming it creates a fake compiler PID.
        compiler = Path(self.environment["OPAM_SWITCH_PREFIX"]) / "bin/coqc"
        shutil.copy2("/bin/sleep", compiler)
        self.environment.update(ZESU_WRITER_ID="writer-0", ZESU_MAX_COQC="48")
        self.fixture.lock.write_text(f"state=held holder=fixture pid={os.getpid()} start=x\n")
        snapshot = self.root / "compiler-pids"
        snapshot.write_text("")
        (self.fixture.bin / "pgrep").write_text('#!/bin/sh\ncat "$FAKE_COMPILER_PIDS"\n')
        self.environment["FAKE_COMPILER_PIDS"] = str(snapshot)
        # A direct Bash shebang gives the same wrapper body comm=coqc.
        # The production env/Bash shebang can report comm=bash instead.
        self.wrapper.write_text(self.wrapper.read_text().replace(
            "#!/usr/bin/env bash", "#!/bin/bash", 1))
        process = subprocess.Popen([str(self.wrapper), "30"], env=self.environment,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        tokens = []
        guard = self.root / "tools/resource_guard.sh"
        try:
            deadline = time.monotonic() + 3
            child = None
            while time.monotonic() < deadline:
                markers = list((Path(self.environment["ZESU_GUARD_STATE"]) /
                                "coqc-reservations").glob("*"))
                candidates = []
                for marker in markers:
                    try:lines = marker.read_text().splitlines()
                    except FileNotFoundError:continue
                    if lines:candidates.append(lines[0])
                candidates = [pid for pid in candidates if pid.isdigit()
                              and Path(f"/proc/{pid}/comm").exists()
                              and Path(f"/proc/{pid}/comm").read_text().strip() == "coqc"
                              and Path(f"/proc/{pid}/exe").resolve() == compiler]
                if candidates:
                    child = candidates[0]
                    break
                time.sleep(0.02)
            self.assertIsNotNone(child)
            self.assertEqual(Path(f"/proc/{process.pid}/comm").read_text().strip(), "coqc")
            snapshot.write_text(f"{process.pid}\n{child}\n")
            # Both raw comm entries are coqc. The guard reports one compiler.
            result = subprocess.run([str(guard), "hold"],
                                    env={**self.environment, "ZESU_MAX_COQC": "2"},
                                    capture_output=True, text=True, timeout=3)
            self.assertEqual(result.stdout.strip(), "none")
            state = Path(self.environment["ZESU_GUARD_STATE"])
            marker = next((state / "coqc-reservations").iterdir())
            self.assertEqual(marker.read_text().splitlines()[0], child)
            # One live writer compiler plus fifteen confirmed writer slots fits
            # alongside 32 conservatively counted external compiler PIDs.
            snapshot.write_text(f"{process.pid}\n{child}\n" +
                                "".join(f"{9000000 + i}\n" for i in range(32)))
            for i in range(1, 16):
                result = subprocess.run([str(guard), "reserve-coqc", str(os.getpid())],
                                        env={**self.environment, "ZESU_WRITER_ID": f"writer-{i // 2}"},
                                        capture_output=True, text=True, timeout=3)
                self.assertEqual(result.returncode, 0, result.stderr)
                tokens.append(result.stdout.strip())
                result = subprocess.run([str(guard), "confirm-coqc", tokens[-1]],
                                        env={**self.environment, "ZESU_WRITER_ID": f"writer-{i // 2}"},
                                        capture_output=True, text=True, timeout=3)
                self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(len(list((state / "coqc-reservations").iterdir())), 16)
            request = subprocess.run([str(guard), "reserve-coqc", str(os.getpid())],
                                     env={**self.environment, "ZESU_WRITER_ID": "writer-8"},
                                     check=True, capture_output=True, text=True).stdout.strip()
            waiter = subprocess.Popen([str(guard), "confirm-coqc", request],
                                      env={**self.environment, "ZESU_WRITER_ID": "writer-8"},
                                      stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            try:
                time.sleep(0.2)
                self.assertIsNone(waiter.poll())
            finally:
                waiter.terminate(); waiter.communicate(timeout=3)
        finally:
            process.terminate(); process.communicate(timeout=3)
            if child is not None:
                self.assertFalse(Path(f"/proc/{child}").exists())
            for token in tokens:
                subprocess.run([str(guard), "release-coqc", token], env=self.environment, check=True)

    def test_writer_scratch_routes_to_updated_guard_under_both_gate_states(self):
        # The local guard represents an old worktree and must never run.
        updated = self.root / "updated-guard.sh"
        shutil.copy2(TOOLS / "resource_guard.sh", updated)
        (self.root / "tools/resource_guard.sh").write_text(
            '#!/bin/sh\necho "OLD GUARD USED" >&2; exit 91\n')
        source = self.root / "Probe.v"
        source.write_text("(* Fake compiler input. *)\n")
        build = self.root / "build"
        build.mkdir()
        (build / "trace.csexp").write_bytes(b"")
        (build / "coqc_recipe.json").write_text(json.dumps({
            "command": [str(self.root / "old-coqc"), "Original.v"], "working_dir": str(self.root)}))
        (self.root / "old-coqc").write_text(
            '#!/bin/sh\necho "OLD COMPILER ROUTE USED" >&2; exit 92\n')
        (self.root / "old-coqc").chmod(0o755)
        for state in ("wanted", "held"):
            self.fixture.lock.write_text(f"state={state} holder=fixture pid={os.getpid()} start=x\n")
            result = subprocess.run([str(self.root / "tools/coqc_scratch.sh"), str(source), str(build)],
                                    env={**self.environment, "ZESU_WRITER_ID": "tf2",
                                         "ZESU_RESOURCE_GUARD": str(updated),
                                         "ZESU_SCRATCH_COQC_BINARY": str(self.wrapper)},
                                    capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(self.fixture.lock.exists())
        self.assertEqual(len(self.compiler_events()), 2)

    def test_mcp_launcher_uses_the_explicit_writer_route(self):
        launcher = self.root / "rocq_mcp_guarded.sh"
        shutil.copy2(TOOLS / "rocq_mcp_guarded.sh", launcher)
        updated = self.root / "updated-guard.sh"
        shutil.copy2(TOOLS / "resource_guard.sh", updated)
        server = self.root / "fake-mcp"
        server.write_text('#!/bin/sh\nprintf "%s\n%s\n" "$ROCQ_COQC_BINARY" "$ZESU_RESOURCE_GUARD"\n')
        server.chmod(0o755)
        scope_log = self.root / "server-scope.log"
        systemd = self.fixture.bin / "systemd-run"
        systemd.write_text(
            '#!/bin/sh\nprintf "%s\n" "$@" >> "$FAKE_SCOPE_LOG"\n'
            'while [ "$1" != -- ]; do shift; done; shift; exec "$@"\n')
        result = subprocess.run([str(launcher)],
                                env={**self.environment, "ZESU_WRITER_ID": "tf2",
                                     "ZESU_RESOURCE_GUARD": str(updated),
                                     "ZESU_ROCQ_COQC_WRAPPER": str(self.wrapper),
                                     "ZESU_ROCQ_MCP_BINARY": str(server),
                                     "FAKE_SCOPE_LOG": str(scope_log)},
                                capture_output=True, text=True, timeout=3)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), [str(self.wrapper), str(updated)])
        self.assertIn("MemoryMax=16G", scope_log.read_text())
        self.assertIn("MemorySwapMax=0", scope_log.read_text())

    def test_writer_dune_wrapper_keeps_its_two_slot_limit_during_gate(self):
        guard = self.root / "tools/resource_guard.sh"
        self.fixture.lock.write_text(f"state=held holder=fixture pid={os.getpid()} start=x\n")
        self.environment["ZESU_WRITER_ID"] = "tf2"
        tokens = [subprocess.run([str(guard), "reserve-coqc", str(os.getpid())],
                                env=self.environment, check=True, capture_output=True,
                                text=True).stdout.strip() for _ in range(2)]
        for token in tokens:
            subprocess.run([str(guard), "confirm-coqc", token], env=self.environment,
                           check=True, capture_output=True, text=True, timeout=3)
        source = self.root / "Probe.v"
        source.write_text("(* Fake compiler input. *)\n")
        process = subprocess.Popen([str(self.wrapper), str(source)], env=self.environment,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            time.sleep(0.2)
            self.assertIsNone(process.poll())
            self.assertEqual(self.compiler_events(), [])
            subprocess.run([str(guard), "release-coqc", tokens.pop()], env=self.environment, check=True)
            _, stderr = process.communicate(timeout=3)
            self.assertEqual(process.returncode, 0, stderr)
            self.assertEqual(len(self.compiler_events()), 1)
        finally:
            if process.poll() is None:
                process.terminate()
            process.communicate(timeout=3)
            for token in tokens:
                subprocess.run([str(guard), "release-coqc", token], env=self.environment, check=True)

    def test_mcp_writer_route_keeps_scope_fence_under_gate(self):
        self.prepare_recordless_private_build()
        updated = self.root / "updated-guard.sh"
        shutil.copy2(TOOLS / "resource_guard.sh", updated)
        mcp_wrapper = self.root / "rocq_coqc_guarded.sh"
        shutil.copy2(TOOLS / "rocq_coqc_guarded.sh", mcp_wrapper)
        shutil.copy2(TOOLS / "coqc_findlib.py", self.root / "coqc_findlib.py")
        scope_log = self.root / "scope.log"
        systemd = self.fixture.bin / "systemd-run"
        systemd.write_text(
            '#!/bin/sh\nprintf "%s\n" "$@" >> "$FAKE_SCOPE_LOG"\n'
            'while [ "$1" != -- ]; do shift; done; shift; exec "$@"\n')
        systemd.chmod(0o755)
        source = self.root / "Probe.v"
        source.write_text("(* Fake compiler input. *)\n")
        for state in ("wanted", "held"):
            self.fixture.lock.write_text(f"state={state} holder=fixture pid={os.getpid()} start=x\n")
            result = subprocess.run([str(mcp_wrapper), str(source)],
                                    cwd=self.root, env={**self.environment, "ZESU_WRITER_ID": "tf2",
                                         "ZESU_RESOURCE_GUARD": str(updated),
                                         "FAKE_SCOPE_LOG": str(scope_log)},
                                    capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(self.compiler_events()), 2)
        self.assertIn("MemoryMax=16G", scope_log.read_text())
        self.assertIn("MemorySwapMax=0", scope_log.read_text())
        self.assertIn("-writer-tf2-", scope_log.read_text())
        reservations = Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
        self.assertEqual(list(reservations.iterdir()), [])

    def test_wrapper_rechecks_an_existing_scratch_reservation(self):
        guard = self.root / "tools/resource_guard.sh"
        token = subprocess.run([str(guard), "reserve-coqc", str(os.getpid())],
                               env=self.environment, check=True, text=True,
                               capture_output=True).stdout.strip()
        source = self.root / "Probe.v"
        source.write_text("(* A fake compiler reads this fixture. *)\n")
        self.blocked.write_text("17\n")
        process = subprocess.Popen([str(self.wrapper), str(source)],
                                   env={**self.environment, "ZESU_COQC_RESERVATION": token},
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            time.sleep(0.2)
            self.assertIsNone(process.poll())
            self.assertEqual(self.compiler_events(), [])
            self.blocked.write_text("16\n")
            _, stderr = process.communicate(timeout=3)
            self.assertEqual(process.returncode, 0, stderr)
            self.assertEqual(len(self.compiler_events()), 1)
        finally:
            if process.poll() is None:
                process.terminate()
            process.communicate(timeout=3)
            subprocess.run([str(guard), "release-coqc", token],
                           env=self.environment, check=True)

    def test_config_queries_do_not_consume_slots_while_blocked(self):
        self.blocked.write_text("17\n")
        result = subprocess.run([str(self.wrapper), "--print-version", "-boot", "-noinit"],
                                env=self.environment, capture_output=True, text=True,
                                timeout=3)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "8.19.2 4.14.4")
        self.assertEqual(self.compiler_events(), [])
        state = Path(self.environment["ZESU_GUARD_STATE"])
        self.assertFalse((state / "coqc-reservations").exists())

    def test_scratch_recipe_reuses_one_reservation_with_dune_wrapper(self):
        self.environment["ZESU_MAX_COQC"] = "1"
        self.environment.pop("OPAM_SWITCH_PREFIX")
        self.environment["ISLARIS_REPO"] = str(self.root / "switch")
        source = self.root / "Probe.v"
        source.write_text("(* Only the fake compiler reads this fixture. *)\n")
        build = self.root / "build"
        build.mkdir()
        (build / "trace.csexp").write_bytes(b"")
        (build / "coqc_recipe.json").write_text(json.dumps({
            "command": [str(self.wrapper), "Original.v"],
            "working_dir": str(self.root),
        }))
        result = subprocess.run([str(self.root / "tools/coqc_scratch.sh"),
                                 str(source), str(build)], env=self.environment,
                                capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(self.compiler_events()), 1)
        reservations = Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
        self.assertEqual(list(reservations.iterdir()), [])

    def test_three_compiler_routes_use_one_slot_and_one_fence(self):
        self.environment.update(ZESU_MAX_COQC="1", ZESU_WRITER_ID="tf2")
        self.fixture.lock.write_text(f"state=held holder=fixture pid={os.getpid()} start=x\n")
        source = self.root / "Probe.v"
        source.write_text("(* Fake compiler input. *)\n")
        build = self.root / "build"
        build.mkdir()
        (build / "trace.csexp").write_bytes(b"")
        compiler = Path(self.environment["OPAM_SWITCH_PREFIX"]) / "bin/coqc"
        (build / "coqc_recipe.json").write_text(json.dumps({
            "command": [str(compiler), "Original.v"], "working_dir": str(self.root)}))
        scratch = [str(self.root / "tools/coqc_scratch.sh"), str(source), str(build)]
        guard = self.root / "tools/resource_guard.sh"
        routes = ([str(self.wrapper), str(source)],
                  [str(self.root / "tools/dune_coqc_guarded.sh"), str(source)], scratch,
                  [str(guard), "scope", "outer", "--", *scratch])
        for route in routes:
            with self.subTest(route=route):
                self.scope_log.unlink(missing_ok=True)
                self.events.unlink(missing_ok=True)
                result = subprocess.run(route, env=self.environment, capture_output=True,
                                        text=True, timeout=5)
                self.assertEqual(result.returncode, 0, result.stderr)
                events = self.compiler_events()
                self.assertEqual(len(events), 1)
                self.assertEqual(events[0]["slots"], 1)
                self.assertEqual(events[0]["cpu"], 2400)
                self.assertEqual(events[0]["scope"], events[0]["token"])
                scopes = [json.loads(line) for line in self.scope_log.read_text().splitlines()]
                self.assertEqual(len(scopes), 1)
                self.assertIn("MemoryMax=16G", scopes[0])
                self.assertIn("MemorySwapMax=0", scopes[0])
                reservations = Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
                self.assertEqual(list(reservations.iterdir()), [])

    def test_dune_checks_each_compiler_with_its_gate_owner_exemption(self):
        dune = shutil.which("dune")
        if dune is None:
            prefix = Path(os.environ.get("OPAM_SWITCH_PREFIX", Path.home() / "islaris/_opam"))
            dune = str(prefix / "bin/dune")
        if not Path(dune).is_file():
            self.skipTest("Dune is unavailable for the isolated fixture")
        self.environment["PATH"] = f"{self.fixture.bin}:{self.root / 'switch/_opam/bin'}:{Path(dune).parent}:{os.environ['PATH']}"
        self.wrapper.unlink()
        (self.root / "dune-project").write_text("(lang dune 3.8)\n(using coq 0.8)\n")
        shutil.copy2(TOOLS.parent / "dune", self.root / "dune")
        proof = self.root / "Fixture"
        proof.mkdir()
        (proof / "dune").write_text("(coq.theory (name Fixture) (stdlib no) (mode vo))\n")
        for name in ("First", "Second"):
            (proof / f"{name}.v").write_text("(* Only the fake compiler reads this fixture. *)\n")
        coqdep = self.fixture.bin / "coqdep"
        coqdep.write_text(
            "#!/usr/bin/env python3\nimport pathlib,sys\n"
            "for x in sys.argv[1:]:\n"
            " if x.endswith('.v'):\n"
            "  p=pathlib.Path(x); dep=' '+str(p.with_name('First.vo')) if p.stem=='Second' else ''\n"
            "  print(str(p.with_suffix('.vo'))+': '+x+dep)\n")
        coqdep.chmod(0o755)
        self.fixture.lock.write_text(f"state=wanted holder=fixture pid={os.getpid()} start=x\n")
        process = subprocess.Popen(
            [dune, "build", "--root", str(self.root), "--cache=disabled", "-j1",
             "--trace-file", str(self.root / "_build/trace.csexp"), "@Fixture/all"],
            env={**self.environment, "ZESU_IN_GATE": "1", "FAKE_BLOCK_AFTER_FIRST": "1"},
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, cwd=self.root)
        try:
            deadline = time.monotonic() + 10
            log = Path(self.environment["ZESU_GUARD_STATE"]) / "guard.log"
            while time.monotonic() < deadline and process.poll() is None:
                if log.exists() and "blocked 17" in log.read_text():
                    break
                time.sleep(0.02)
            if process.poll() is not None:
                _, stderr = process.communicate()
                self.fail(f"Dune fixture exited before its blocked hold: {stderr}")
            self.assertEqual(len(self.compiler_events()), 1)
            self.assertIn("blocked 17", log.read_text())
            self.blocked.write_text("16\n")
            _, stderr = process.communicate(timeout=10)
            self.assertEqual(process.returncode, 0, stderr)
            self.assertEqual(len(self.compiler_events()), 2)
            record = json.loads((self.root / "_build/coqc-ocamlpath.json").read_text())
            self.assertEqual(record["workspace"], str(self.root.resolve()))
            self.assertEqual(record["private_build"], str((self.root / "_build").resolve()))
            self.assertEqual((self.root / "_build/default").resolve(),
                             self.root / "_build/default")
            self.assertTrue(all(event["OCAMLPATH"] == record["OCAMLPATH"]
                                for event in self.compiler_events()))
            self.assertTrue(self.fixture.lock.exists())
            recipe = compiler_recipe((self.root / "_build/trace.csexp").read_bytes())
            self.assertIsNotNone(recipe)
            self.assertEqual(Path(recipe["command"][0]).name, "coqc")
            reservations = Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
            self.assertEqual(list(reservations.iterdir()), [])
        finally:
            if process.poll() is None:
                process.terminate()
            process.communicate(timeout=3)


class McpThresholdTest(unittest.TestCase):
    @staticmethod
    def guard_default_memory():
        result = subprocess.run([str(TOOLS / "resource_guard.sh"), "gate-module-limit"],
                                env=test_guard.fixture_environment(),
                                check=True, capture_output=True, text=True)
        return result.stdout.strip()

    def test_mcp_wrappers_preserve_explicit_hold_and_default_fence(self):
        self.check_wrappers("215")

    def test_mcp_wrappers_retain_default_hold_and_default_fence(self):
        self.check_wrappers(None)

    def test_mcp_wrappers_propagate_the_configured_gate_fence(self):
        for limit in ("6", "16", "32"):
            with self.subTest(limit=limit):
                self.check_wrappers(None, limit)

    def test_mcp_wrappers_reject_invalid_gate_fences_before_launch(self):
        for limit in ("", "5", "33", "64", "-6", "6.5", "invalid"):
            with self.subTest(limit=limit):
                self.check_wrappers(None, limit, accepted=False)

    def check_wrappers(self, hold, limit=None, accepted=True):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "bin"
            binary.mkdir()
            events = root / "events.jsonl"
            stub = ("#!/usr/bin/env python3\nimport json,os,sys\n"
                    "with open(os.environ['WRAPPER_EVENTS'],'a') as f:\n"
                    " f.write(json.dumps({'hold':os.environ.get('ZESU_HOLD_GIB'),"
                    "'memory':os.environ.get('ZESU_MODULE_LIMIT_GIB'),"
                    "'pet_rss_mb':os.environ.get('ROCQ_MAX_PET_RSS_MB'),"
                    "'arguments':sys.argv[1:]})+'\\n')\n")
            for name in ("systemd-run", "guard", "coqc", "rocq-mcp"):
                path = binary / name
                path.write_text(stub)
                path.chmod(0o755)
            env = test_guard.fixture_environment()
            env.update(PATH=str(binary) + ":" + env.get("PATH", ""),
                       WRAPPER_EVENTS=str(events), ZESU_MODULE_LIMIT_GIB="99",
                       ZESU_RESOURCE_GUARD=str(binary / "guard"),
                       ZESU_ROCQ_MCP_BINARY=str(binary / "rocq-mcp"),
                       ZESU_ROCQ_COQC_BINARY=str(binary / "coqc"))
            if hold is not None:
                env["ZESU_HOLD_GIB"] = hold
            if limit is not None:
                env["ZESU_GATE_MODULE_LIMIT_GIB"] = limit
            for name in ("rocq_mcp_guarded.sh", "rocq_coqc_guarded.sh"):
                events.unlink(missing_ok=True)
                result = subprocess.run([str(TOOLS / name), "Fixture.v"],
                                        cwd=root, env=env, capture_output=True,
                                        text=True, timeout=5)
                if not accepted:
                    self.assertEqual(result.returncode, 2, result.stderr)
                    self.assertIn("integer from 6 through 32", result.stderr)
                    self.assertFalse(events.exists())
                    continue
                self.assertEqual(result.returncode, 0, result.stderr)
                rows = [json.loads(line) for line in events.read_text().splitlines()]
                self.assertTrue(rows)
                self.assertTrue(all(row["hold"] == (hold or "180") for row in rows))
                memory = limit or McpThresholdTest.guard_default_memory()
                self.assertTrue(all(row["memory"] == memory for row in rows))
                if name == "rocq_mcp_guarded.sh":
                    self.assertIn(f"MemoryMax={memory}G", rows[0]["arguments"])
                    self.assertIn("MemorySwapMax=0", rows[0]["arguments"])
                    self.assertTrue(all(row["pet_rss_mb"] == str(int(memory) * 1024)
                                        for row in rows))


if __name__ == "__main__":
    unittest.main()
