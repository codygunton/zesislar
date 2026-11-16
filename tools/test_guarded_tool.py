"""Check that guarded_tool.sh fences a heavy tool in its own workload scope."""
import json
import os
import re
import shutil
from pathlib import Path
import subprocess
import tempfile
import unittest

WRAPPER = Path(__file__).with_name("guarded_tool.sh")
TOOLS = Path(__file__).resolve().parent
LITERAL = "pid $$ home $HOME braces ${HOME}"
PASSTHROUGH_GUARD = """#!/bin/sh
[ "$1" = parent-setup ] && exit 0
shift 2
exec "$@"
"""


def user_systemd_available():
    if shutil.which("systemd-run") is None:
        return False
    probe = subprocess.run(["systemd-run", "--user", "--scope", "--quiet", "--collect", "--", "true"],
                           capture_output=True, timeout=60)
    return probe.returncode == 0


RECORDER = """#!/usr/bin/env python3
import json, os, sys
with open(os.environ['TEST_LOG'], 'a') as stream:
    stream.write(json.dumps({'tool': os.path.basename(sys.argv[0]), 'args': sys.argv[1:]}) + '\\n')
"""


class GuardedTool(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.log = root / "log.jsonl"
        bin_dir = root / "bin"
        bin_dir.mkdir()
        for name in ("systemd-run", "resource_guard.sh"):
            path = bin_dir / name
            path.write_text(RECORDER)
            path.chmod(0o755)
        self.environment = {**os.environ, "TEST_LOG": str(self.log),
                            "PATH": f"{bin_dir}:{os.environ['PATH']}",
                            "ZESU_RESOURCE_GUARD": str(bin_dir / "resource_guard.sh")}
        self.environment.pop("ZESU_TOOL_MEMORY_GIB", None)

    def run_wrapper(self, *arguments):
        return subprocess.run([str(WRAPPER), *arguments], env=self.environment,
                              capture_output=True, text=True, timeout=60)

    def calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def test_default_scope_is_16_gib_in_the_workload_parent(self):
        result = self.run_wrapper("--", "python3", "gen.py", "--pass", "forward")
        self.assertEqual(result.returncode, 0, result.stderr)
        setup, launch = self.calls()
        self.assertEqual(setup, {"tool": "resource_guard.sh", "args": ["parent-setup"]})
        self.assertEqual(launch["tool"], "systemd-run")
        args = launch["args"]
        for expected in ("--user", "--scope", "--slice=zesuworkloads.slice", "--expand-environment=no",
                         "MemoryMax=16G", "MemorySwapMax=0"):
            self.assertIn(expected, args)
        tail = args[args.index("--") + 1:]
        self.assertEqual(tail[1:], ["parent-exec", "--", "python3", "gen.py", "--pass", "forward"])
        self.assertTrue(tail[0].endswith("resource_guard.sh"))
        unit = next(a for a in args if a.startswith("--unit="))
        self.assertTrue(unit.startswith("--unit=zesutool-python3-"), unit)

    def test_memory_option_and_environment_set_the_fence(self):
        result = self.run_wrapper("--memory", "48", "--", "render")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("MemoryMax=48G", self.calls()[1]["args"])
        self.log.unlink()
        self.environment["ZESU_TOOL_MEMORY_GIB"] = "24"
        result = self.run_wrapper("render")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("MemoryMax=24G", self.calls()[1]["args"])

    def test_invalid_memory_or_missing_command_refuses_before_launch(self):
        for arguments in (("--memory", "0", "--", "x"), ("--memory", "4x", "--", "x"),
                          ("--memory",), ("--",)):
            with self.subTest(arguments=arguments):
                result = self.run_wrapper(*arguments)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertFalse(self.log.exists())

    @unittest.skipUnless(os.environ.get("ZESU_GUARDED_TOOL_LIVE") == "1", "opt-in live systemd scope")
    def test_live_scope_runs_inside_the_parent_with_oom_preference(self):
        environment = {k: v for k, v in os.environ.items() if not k.startswith("ZESU_")}
        result = subprocess.run(
            [str(WRAPPER), "--memory", "1", "--", "python3", "-c",
             "print(open('/proc/self/cgroup').read().strip());"
             "print(open('/proc/self/oom_score_adj').read().strip())"],
            env=environment, capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stderr)
        cgroup, oom = result.stdout.splitlines()
        self.assertIn("/zesuworkloads.slice/zesutool-python3-", cgroup)
        self.assertEqual(oom, "1000")


class ExpandEnvironment(unittest.TestCase):
    """systemd-run expands $VAR and turns $$ into $ unless --expand-environment=no (systemd 262)."""

    def test_every_systemd_run_call_in_tools_turns_expansion_off(self):
        call = re.compile(r"""systemd-run['"]?\s*,?\s*['"]?--user""")
        missing = []
        for path in sorted(TOOLS.rglob("*")):
            if (not path.is_file() or path.name.startswith("test_") or "__pycache__" in path.parts
                    or path.suffix not in (".sh", ".py", ".service", "")):
                continue
            try:
                text = path.read_text()
            except UnicodeDecodeError:
                continue
            for match in call.finditer(text):
                command = re.split(r"""\s--\s|'--',|"--",""", text[match.start():])[0]
                if "--expand-environment=no" not in command:
                    missing.append(f"{path.relative_to(TOOLS)}:{text.count(chr(10), 0, match.start()) + 1}")
        self.assertEqual(missing, [])

    @unittest.skipUnless(user_systemd_available(), "needs a systemd user manager")
    def test_live_command_with_dollars_reaches_the_job_unchanged(self):
        with tempfile.TemporaryDirectory() as temp:
            guard = Path(temp) / "resource_guard.sh"
            guard.write_text(PASSTHROUGH_GUARD)
            guard.chmod(0o755)
            environment = {k: v for k, v in os.environ.items() if not k.startswith("ZESU_")}
            environment["ZESU_RESOURCE_GUARD"] = str(guard)
            result = subprocess.run(
                [str(WRAPPER), "--memory", "1", "--", "python3", "-c", "import sys; print(sys.argv[1])", LITERAL],
                env=environment, capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, LITERAL + "\n")

    @unittest.skipUnless(user_systemd_available(), "needs a systemd user manager")
    def test_live_command_status_and_signal_reach_the_caller(self):
        # guarded_tool execs into the scope, so a shell caller sees 7 or 128+15.
        with tempfile.TemporaryDirectory() as temp:
            guard = Path(temp) / "resource_guard.sh"
            guard.write_text(PASSTHROUGH_GUARD)
            guard.chmod(0o755)
            environment = {k: v for k, v in os.environ.items() if not k.startswith("ZESU_")}
            environment["ZESU_RESOURCE_GUARD"] = str(guard)
            for script, expected in (("exit 7", 7), ("kill -TERM $$", -15)):
                with self.subTest(script=script):
                    result = subprocess.run([str(WRAPPER), "--memory", "1", "--", "sh", "-c", script],
                                            env=environment, capture_output=True, text=True, timeout=120)
                    self.assertEqual(result.returncode, expected, result.stderr)


if __name__ == "__main__":
    unittest.main()
