"""Check owned guard staging without a proof or compiler run."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
import guard_workspace as guard


ROOT = Path(__file__).resolve().parents[1]


class GuardWorkspaceTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.source = self.root / "source"
        self.owned = self.root / "owned"
        for name in guard.GUARD_RUNTIME_FILES:
            path = self.source / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(name + "\n")
            path.chmod(0o755)

    def row(self, path=None):
        path = path or self.source / "tools/resource_guard.sh"
        return {"path": str(path), "sha256": guard.digest(path)}

    def test_identical_guard_parameters_validate_once(self):
        row = self.row()
        self.assertEqual(guard.checked_bindings([row, row]), [row])

    def test_path_aliases_validate_once(self):
        row = self.row()
        alias = dict(row, path=str(self.source / "tools/../tools/resource_guard.sh"))
        self.assertEqual(guard.checked_bindings([row, alias]), [row])

    def test_conflicting_aliases_refuse(self):
        row = self.row()
        with self.assertRaisesRegex(ValueError, "conflicting hashes"):
            guard.checked_bindings([row, dict(row, sha256="0" * 64)])

    def test_changed_binding_refuses(self):
        row = self.row()
        Path(row["path"]).write_text("changed")
        with self.assertRaisesRegex(ValueError, "binding changed"):
            guard.checked_bindings([row])

    def test_missing_registry_refuses_before_copy(self):
        (self.source / "tools/run_registry.py").unlink()
        with self.assertRaisesRegex(ValueError, "run_registry.py"):
            guard.stage_guard_tools(self.source, self.owned)
        self.assertFalse(self.owned.exists())

    def test_missing_nested_helper_refuses_before_copy(self):
        (self.source / "tools/det/coqc_slots.py").unlink()
        with self.assertRaisesRegex(ValueError, "coqc_slots.py"):
            guard.stage_guard_tools(self.source, self.owned)
        self.assertFalse(self.owned.exists())

    def test_complete_closure_preserves_paths_modes_and_inodes(self):
        copies = guard.stage_guard_tools(self.source, self.owned)
        self.assertEqual(len(copies), len(guard.GUARD_RUNTIME_FILES))
        guard.validate_guard_tools(self.owned, copies)
        for row in copies:
            source, target = Path(row["source"]["path"]), Path(row["owned"]["path"])
            self.assertEqual(target, self.owned / row["relative_path"])
            self.assertEqual(target.read_bytes(), source.read_bytes())
            self.assertEqual(target.stat().st_mode & 0o777, 0o755)
            self.assertNotEqual((target.stat().st_dev, target.stat().st_ino),
                                (source.stat().st_dev, source.stat().st_ino))

    def test_changed_expected_closure_refuses_before_copy(self):
        expected = {name: guard.digest(self.source / name) for name in guard.GUARD_RUNTIME_FILES}
        expected["tools/run_registry.py"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "binding changed"):
            guard.stage_guard_tools(self.source, self.owned, expected=expected)
        self.assertFalse(self.owned.exists())

    def test_incomplete_expected_closure_refuses(self):
        with self.assertRaisesRegex(ValueError, "closure is incomplete"):
            guard.stage_guard_tools(self.source, self.owned, expected={})

    def test_changed_owned_helper_refuses_before_admission(self):
        copies = guard.stage_guard_tools(self.source, self.owned)
        (self.owned / "tools/det/prom.py").write_text("changed")
        with self.assertRaisesRegex(ValueError, "binding changed"):
            guard.validate_guard_tools(self.owned, copies)

    def test_incomplete_and_repeated_copy_records_refuse(self):
        copies = guard.stage_guard_tools(self.source, self.owned)
        for rows in [copies[:-1], copies + copies[:1]]:
            with self.subTest(count=len(rows)), self.assertRaisesRegex(ValueError, "closure is incomplete or repeated"):
                guard.validate_guard_tools(self.owned, rows)

    def test_source_workspace_refuses(self):
        with self.assertRaisesRegex(ValueError, "must differ"):
            guard.stage_guard_tools(self.source, self.source)

    def test_external_destination_directory_refuses(self):
        self.owned.mkdir()
        (self.owned / "tools").symlink_to(self.source / "tools", target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "destination leaves"):
            guard.stage_guard_tools(self.source, self.owned)
        self.assertEqual((self.source / "tools/resource_guard.sh").read_text(),
                         "tools/resource_guard.sh\n")

    def test_source_hardlink_refuses_before_any_copy(self):
        target = self.owned / "tools/run_registry.py"
        target.parent.mkdir(parents=True)
        target.hardlink_to(self.source / "tools/run_registry.py")
        with self.assertRaisesRegex(ValueError, "shares its source inode"):
            guard.stage_guard_tools(self.source, self.owned)
        self.assertFalse((self.owned / "tools/resource_guard.sh").exists())
        self.assertEqual(target.read_text(), "tools/run_registry.py\n")

    @unittest.skipUnless(os.environ.get("ZESU_GUARD_WORKSPACE_LIVE") == "1", "opt-in owned guard control")
    def test_real_owned_guarded_payload(self):
        destination = os.environ.get("ZESU_GUARD_WORKSPACE_LIVE_OUTPUT")
        live_root = Path(destination).parent if destination else self.root
        owned = live_root / "owned"
        copies = guard.stage_guard_tools(ROOT, owned)
        guard.validate_guard_tools(owned, copies)
        result = live_root / "payload.json"
        payload = live_root / "payload.py"
        payload.write_text('''import json,os,sys
from pathlib import Path
membership=next(x[3:] for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
scope=Path('/sys/fs/cgroup')/membership.lstrip('/')
aggregate=scope.parent
parent=aggregate.parent
assert parent.name=='zesuworkloads.slice'
assert aggregate.name.startswith('zesuworkloads-aggregate')
for group,expected in [(scope,68719476736),(aggregate,68719476736),(parent,187904819200)]:
 assert int((group/'memory.max').read_text())==expected
 assert (group/'memory.swap.max').read_text().strip()=='0'
ticks=int(Path('/proc/self/stat').read_text().rsplit(')',1)[1].split()[19])
data={'pid':os.getpid(),'startticks':ticks,'cgroup':membership,'scope_bytes':68719476736,'aggregate_bytes':68719476736,'parent_bytes':187904819200,'swap_bytes':0,'proof_calls':0,'compiler_calls':0}
Path(sys.argv[1]).write_text(json.dumps(data,indent=2)+'\\n')
''')
        environment = {key: value for key, value in os.environ.items()
                       if not key.startswith(("ZESU_", "ROCQ_", "COQC_"))}
        environment.update(ZESU_RUN_REGISTRY=str(live_root / "registry"),
                           ZESU_BATCH_LIMIT="64G", ZESU_MODULE_LIMIT_GIB="64",
                           ZESU_DIAGNOSTIC_PROBE="1", ZESU_PROBE_ISSUE="10",
                           ZESU_PROOF_CPU_LIMIT="unlimited", PYTHONDONTWRITEBYTECODE="1")
        executable = owned / "tools/resource_guard.sh"
        command = [str(executable), "batch", "guard-workspace-control", "--",
                   str(executable), "scope", "guard-workspace-payload", "--cpu", "unlimited", "--",
                   sys.executable, str(payload), str(result)]
        reply = subprocess.run(command, cwd=ROOT, env=environment, capture_output=True, text=True)
        self.assertEqual(reply.returncode, 0, reply.stderr)
        observed = json.loads(result.read_text())
        runs = json.loads((live_root / "registry/runs.json").read_text())["runs"]
        self.assertTrue(runs)
        self.assertTrue(all(row["status"] == "completed" for row in runs.values()))
        observed.update(command=command, returncode=reply.returncode, registry=runs,
                        helper_bindings=copies,
                        aggregate_absent=not (Path('/sys/fs/cgroup') / observed['cgroup'].lstrip('/')).parent.exists())
        self.assertTrue(observed["aggregate_absent"])
        if destination:
            Path(destination).write_text(json.dumps(observed, indent=2) + "\n")


if __name__ == "__main__":
    unittest.main()
