"""Exercise Dune compiler admission with a fake compiler and private guard state."""

import json
import os
import shutil
import subprocess
import time
import unittest
from pathlib import Path

import test_guard
from coqc_recipe import compiler_recipe


TOOLS = Path(__file__).resolve().parent


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
        for name in ("resource_guard.sh", "dune_coqc_guarded.sh", "coqc_scratch.sh",
                     "coqc_recipe.py", "guard-bin/dune"):
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
            "os.write(fd,(json.dumps({'source':str(source),'args':args,'token':os.environ.get('ZESU_COQC_RESERVATION'),'scope':os.environ.get('ZESU_COQC_SCOPE'),'slots':len(list(pathlib.Path(os.environ['ZESU_GUARD_STATE'],'coqc-reservations').iterdir())),'cpu':resource.getrlimit(resource.RLIMIT_CPU)[0]})+'\\n').encode());os.close(fd)\n"
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

    def test_failed_snapshot_prevents_every_compiler_route(self):
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
            for route in routes:
                with self.subTest(status=status, route=route):
                    result = subprocess.run(route, env=self.environment, capture_output=True,
                                            text=True, timeout=5)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("compiler snapshot failed", result.stderr)
                    self.assertEqual(self.compiler_events(), [])
                    self.assertFalse(self.scope_log.exists())
                    reservations = Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
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
        self.assertIn("MemoryMax=6G", scope_log.read_text())
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
        updated = self.root / "updated-guard.sh"
        shutil.copy2(TOOLS / "resource_guard.sh", updated)
        mcp_wrapper = self.root / "rocq_coqc_guarded.sh"
        shutil.copy2(TOOLS / "rocq_coqc_guarded.sh", mcp_wrapper)
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
                                    env={**self.environment, "ZESU_WRITER_ID": "tf2",
                                         "ZESU_RESOURCE_GUARD": str(updated),
                                         "FAKE_SCOPE_LOG": str(scope_log)},
                                    capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(self.compiler_events()), 2)
        self.assertIn("MemoryMax=6G", scope_log.read_text())
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
                self.assertEqual(events[0]["cpu"], 1200)
                self.assertEqual(events[0]["scope"], events[0]["token"])
                scopes = [json.loads(line) for line in self.scope_log.read_text().splitlines()]
                self.assertEqual(len(scopes), 1)
                self.assertIn("MemoryMax=6G", scopes[0])
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
            [dune, "build", "--root", str(self.root), "--cache=disabled", "-j1", "@Fixture/all"],
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


if __name__ == "__main__":
    unittest.main()
