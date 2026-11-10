"""Check measured reservations without launching compilers."""

from contextlib import redirect_stdout
from copy import deepcopy
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools import module_memory as memory


class ModuleMemoryTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.compiler = self.root / "coqc"
        self.compiler.write_bytes(b"compiler")
        (self.root / "Small.v").write_text("Check nat.\n")
        (self.root / "Large.v").write_text("Check bool.\n")
        self.profile_path = self.root / "cache/profile.json"

    def bound(self, source="Small.v", arguments=None):
        return memory.binding(arguments or ["-q", source], self.root, self.compiler)

    def record(self, source="Small.v", peak=600 * 1024 ** 2, arguments=None):
        name, bound = self.bound(source, arguments)
        return memory.record_measurement(self.profile_path, name, bound, peak)

    def profile(self, rows=None):
        for source, peak in rows or [("Small.v", 600 * 1024 ** 2)]:
            self.record(source, peak)
        return memory.load_profile(self.profile_path)

    def claim(self, source="Small.v", arguments=None, **keywords):
        return memory.module_claim(memory.load_profile(self.profile_path),
                                   arguments or ["-q", source], self.root, self.compiler, **keywords)

    def test_small_modules_use_the_floor_and_large_modules_use_measured_margin(self):
        self.profile([("Small.v", 100 * 1024 ** 2), ("Large.v", 8 * memory.GIB)])
        self.assertEqual(self.claim("Small.v")["claim_bytes"], memory.FLOOR_BYTES)
        self.assertEqual(self.claim("Large.v")["claim_bytes"],
                         8 * memory.GIB * memory.MARGIN_NUMERATOR // memory.MARGIN_DENOMINATOR)

    def test_booking_covers_the_guard_growth_rule_on_resident_set(self):
        name, bound = self.bound("Small.v")
        memory.record_measurement(self.profile_path, name, bound, 500 * 1024 ** 2,
                                  rss_peak_bytes=600 * 1024 ** 2)
        self.assertEqual(self.claim()["claim_bytes"], 900 * 1024 ** 2)
        memory.record_measurement(self.profile_path, name, bound, 400 * 1024 ** 2,
                                  rss_peak_bytes=500 * 1024 ** 2)
        row = memory.load_profile(self.profile_path)["modules"]["Small.v"]
        self.assertEqual((row["peak_bytes"], row["rss_peak_bytes"]), (500 * 1024 ** 2, 600 * 1024 ** 2))
        self.assertEqual(memory.booking(memory.GIB, 16 * memory.GIB, None),
                         memory.GIB * memory.MARGIN_NUMERATOR // memory.MARGIN_DENOMINATOR)

    def test_measured_claim_never_exceeds_the_physical_fence(self):
        self.profile([("Large.v", 15 * memory.GIB)])
        self.assertEqual(self.claim("Large.v", fallback_bytes=16 * memory.GIB)["claim_bytes"], 16 * memory.GIB)
        self.assertEqual(self.claim("Large.v", fallback_bytes=64 * memory.GIB)["claim_bytes"],
                         -(-15 * memory.GIB * memory.MARGIN_NUMERATOR // memory.MARGIN_DENOMINATOR))

    def test_repeated_module_uses_the_largest_measurement(self):
        self.profile([("Small.v", 2 * memory.GIB), ("Small.v", memory.GIB)])
        row = memory.load_profile(self.profile_path)["modules"]["Small.v"]
        self.assertEqual((row["peak_bytes"], row["minimum_peak_bytes"], row["observations"]),
                         (2 * memory.GIB, memory.GIB, 2))
        self.assertEqual(self.claim()["claim_bytes"], memory.booking(2 * memory.GIB, 16 * memory.GIB))

    def test_changed_source_books_the_fence_until_it_is_measured_again(self):
        self.profile([("Small.v", 2 * memory.GIB)])
        (self.root / "Small.v").write_text("Check unit.\n")
        self.assertEqual((self.claim()["claim_bytes"], self.claim()["reason"]),
                         (16 * memory.GIB, "changed_source"))
        self.record("Small.v", memory.GIB)
        row = memory.load_profile(self.profile_path)["modules"]["Small.v"]
        self.assertEqual((row["peak_bytes"], row["observations"]), (memory.GIB, 1))
        self.assertEqual(self.claim()["reason"], "measured_module")

    def test_invalid_peaks_refuse(self):
        for peak in (-1, 0, None, True, 1.5):
            with self.subTest(peak=peak), self.assertRaises(ValueError):
                self.record(peak=peak)

    def test_ambiguous_or_escaping_source_paths_refuse(self):
        for arguments in ([], ["Small.v", "Large.v"], ["../Small.v"], ["/Small.v"], ["./Small.v"]):
            with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                memory.module_source(arguments)

    def test_changed_compiler_uses_the_full_fallback(self):
        self.profile()
        self.compiler.write_bytes(b"changed")
        value = self.claim()
        self.assertEqual((value["claim_bytes"], value["reason"]), (16 * memory.GIB, "changed_compiler"))

    def test_unknown_module_books_its_directory_prior(self):
        self.profile([("Small.v", 3 * memory.GIB)])
        value = self.claim("Large.v")
        self.assertEqual((value["claim_bytes"], value["reason"]), (3 * memory.GIB * 3 // 2, "directory_prior"))
        # The prior covers the guard growth rule on a resident set larger than the scope peak.
        name, bound = self.bound("Small.v")
        memory.record_measurement(self.profile_path, name, bound, memory.GIB, rss_peak_bytes=4 * memory.GIB)
        self.assertEqual(self.claim("Large.v")["claim_bytes"], 6 * memory.GIB)

    def test_unknown_module_in_an_unmeasured_directory_keeps_the_full_fallback(self):
        self.profile([("Small.v", 3 * memory.GIB)])
        (self.root / "sub").mkdir()
        (self.root / "sub/New.v").write_text("Check nat.\n")
        value = self.claim("sub/New.v")
        self.assertEqual((value["claim_bytes"], value["reason"]), (16 * memory.GIB, "unknown_module"))
        self.assertEqual(memory.directory_prior(memory.load_profile(self.profile_path), "sub/New.v",
                                                16 * memory.GIB), None)

    def test_directory_prior_never_exceeds_the_fallback(self):
        self.profile([("Small.v", 15 * memory.GIB)])
        self.assertEqual(self.claim("Large.v")["claim_bytes"], 16 * memory.GIB)
        self.assertEqual(self.claim("Large.v", fallback_bytes=64 * memory.GIB)["claim_bytes"],
                         15 * memory.GIB * 3 // 2)

    def test_directory_prior_books_at_least_two_gib(self):
        self.profile([("Small.v", 100 * 1024 ** 2)])
        value = self.claim("Large.v")
        self.assertEqual((value["claim_bytes"], value["reason"]), (2 * memory.GIB, "directory_prior"))
        self.assertEqual(memory.directory_prior(memory.load_profile(self.profile_path), "Large.v",
                                                memory.GIB), memory.GIB)

    def test_missing_peak_uses_the_full_fallback(self):
        self.profile()
        profile = memory.load_profile(self.profile_path)
        profile["modules"]["Small.v"]["peak_bytes"] = None
        value = memory.module_claim(profile, ["-q", "Small.v"], self.root, self.compiler)
        self.assertEqual((value["claim_bytes"], value["reason"]), (16 * memory.GIB, "missing_peak"))

    def test_unrecognized_command_uses_the_full_fallback(self):
        self.profile()
        value = self.claim(arguments=["Small.v", "Large.v"])
        self.assertEqual((value["claim_bytes"], value["reason"]), (16 * memory.GIB, "ambiguous_source"))

    def test_only_completed_matching_measurements_allow_small_claims(self):
        fence = 64 * memory.GIB
        for completed, matching in [(False, True), (True, False), (None, True), (1, True)]:
            with self.subTest(completed=completed, matching=matching):
                self.assertEqual(memory.measurement_claim(fence, 3, completed=completed, matching=matching), fence)
        self.assertEqual(memory.measurement_claim(fence, 3, completed=True, matching=True), 5)
        for peak in [None, 0, -1, True, 1.5]:
            with self.subTest(peak=peak):
                self.assertEqual(memory.measurement_claim(fence, peak, completed=True, matching=True), fence)

    def test_older_or_damaged_profiles_read_as_empty(self):
        for text in ('{"schema": "zesu.module-memory.v2", "modules": {"Small.v": {}}}', "{", "[]"):
            with self.subTest(text=text):
                self.profile_path.parent.mkdir(parents=True, exist_ok=True)
                self.profile_path.write_text(text)
                self.assertEqual(memory.load_profile(self.profile_path)["modules"], {})
                self.assertEqual(self.claim()["reason"], "unknown_module")
        self.record()
        self.assertEqual(self.claim()["reason"], "measured_module")

    def test_changed_compiler_arguments_keep_actual_fence(self):
        self.profile()
        result = self.claim(arguments=["-q", "-native-compiler", "no", "Small.v"],
                            fallback_bytes=64 * memory.GIB)
        self.assertEqual((result["claim_bytes"], result["reason"]),
                         (64 * memory.GIB, "changed_arguments"))

    def test_concurrent_writers_keep_every_measurement(self):
        import multiprocessing
        sources = [f"M{index}.v" for index in range(24)]
        for source in sources:
            (self.root / source).write_text(f"(* {source} *)\n")
        jobs = [(str(self.profile_path), source, self.bound(source)[1], (index + 1) * 1024 ** 2)
                for index, source in enumerate(sources)]
        with multiprocessing.get_context("spawn").Pool(8) as pool:
            pool.starmap(memory.record_measurement, jobs)
        modules = memory.load_profile(self.profile_path)["modules"]
        self.assertEqual(set(modules), set(sources))
        self.assertEqual([modules[source]["peak_bytes"] for source in sources],
                         [(index + 1) * 1024 ** 2 for index in range(24)])
        self.assertEqual(list(self.profile_path.parent.glob(".profile-*")), [])

    def test_scope_peak_requires_the_named_guard_scope(self):
        proc, cgroups = self.root / "proc", self.root / "cgroup"
        (proc / "self").mkdir(parents=True)
        leaf = cgroups / "user.slice/zesu-dune-coqc-1.scope"
        leaf.mkdir(parents=True)
        (leaf / "memory.peak").write_text("123456\n")
        (proc / "self/cgroup").write_text("0::/user.slice/zesu-dune-coqc-1.scope\n")
        read = lambda unit: memory.scope_peak(proc=proc, cgroup_root=cgroups, unit=unit)
        self.assertEqual(read("zesu-dune-coqc-1.scope"), 123456)
        self.assertIsNone(read("zesu-dune-coqc-2.scope"))
        self.assertIsNone(read(""))
        (leaf / "memory.peak").unlink()
        self.assertIsNone(read("zesu-dune-coqc-1.scope"))

    def test_admission_cli_passes_the_actual_fence_to_unknown_compilers(self):
        ledger = self.root / "LEDGER.json"
        ledger.write_text('{"fixed_claims": {}, "region_claims": {}}\n')
        with patch("sys.argv", ["module_memory.py", "admission", "--request-bytes", "1",
                               "--available-bytes", "1000000000000", "--fallback-bytes", str(64*memory.GIB)]), \
                patch.object(memory, "reservation_claims", return_value={"claims": [], "growth": [], "unrepresented_compilers": []}) as observed, \
                patch.object(memory, "current_projection", return_value={"fits": True}), \
                patch.object(memory, "read_shell_bookings", return_value={}), \
                patch.dict(memory.os.environ, {"ZESU_CANONICAL_LEDGER": str(ledger),
                                             "ZESU_GATE_LOCK": str(self.root / "gate.lock")}):
            self.assertEqual(memory.main(), 0)
        self.assertEqual(observed.call_args.kwargs['fallback_bytes'], 64*memory.GIB)

    def test_admission_cli_leaves_the_budget_to_ledger_confirm(self):
        ledger = self.root / "LEDGER.json"
        ledger.write_text('{"fixed_claims": {}, "region_claims": {}}\n')
        for count, expected in ((1, ""), (48, "compiler_limit")):
            output = io.StringIO()
            with patch("sys.argv", ["module_memory.py", "admission", "--request-bytes", "1",
                                   "--available-bytes", "1"]), \
                    patch.object(memory, "reservation_claims", return_value={
                        "claims": [memory.GIB] * count, "growth": [], "unrepresented_compilers": []}), \
                    patch.object(memory, "current_projection") as projection, \
                    patch.object(memory, "read_shell_bookings", return_value={}), \
                    patch.dict(memory.os.environ, {"ZESU_CANONICAL_LEDGER": str(ledger),
                                                 "ZESU_GATE_LOCK": str(self.root / "gate.lock")}), \
                    redirect_stdout(output):
                self.assertEqual(memory.main(), 0)
            # One projection per launch, in ledger-confirm; none here.
            projection.assert_not_called()
            self.assertEqual(output.getvalue().split(";")[0].strip(),
                             f"module memory: {expected}" if expected else "")

    def test_owned_loader_resolves_late_controller_booking_import(self):
        import os
        import subprocess
        import sys
        import textwrap

        tools = Path(__file__).resolve().parent
        script = textwrap.dedent("""
            from pathlib import Path
            import sys

            tools = Path(sys.argv[1]).resolve()
            harness = tools / "block/harness"
            code = harness / "code"
            sys.path[:0] = [str(harness), str(code), str(tools / "block"), str(tools)]
            from test_controller_association import ControllerAssociationTests

            fixture = ControllerAssociationTests()
            fixture.setUp()
            try:
                sys.path[:] = [p for p in sys.path
                               if Path(p).resolve() not in (harness, code, tools / "block")]
                for name in ("scope_bookings", "entry_chain",
                             "entry_pilot_checker", "complete_goals_mcp"):
                    sys.modules.pop(name, None)
                sys.path.insert(0, str(tools))
                import module_memory

                f = fixture.f
                sample = module_memory.ScopeReader.claim(
                    f.reader, f.data, f.key, pending_shell=(f.marker, f.token))
                assert sample["verified"], sample
                assert sample["aggregate_verified"], sample
            finally:
                fixture.doCleanups()
        """)
        environment = dict(os.environ)
        environment.pop("PYTHONPATH", None)
        result = subprocess.run([sys.executable, "-c", script, str(tools)],
                                cwd=self.root, env=environment,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_admission_uses_exact_seventy_percent_boundary(self):
        self.assertTrue(memory.admission(40, [30], 100, headroom_bytes=0)["admitted"])
        self.assertEqual(memory.admission(41, [30], 100, headroom_bytes=0)["reason"], "memory_budget")

    def test_admission_preserves_headroom_and_the_compiler_limit(self):
        self.assertFalse(memory.admission(61, [], 100, headroom_bytes=40, slice_max_bytes=100)["admitted"])
        self.assertEqual(memory.admission(1, [1] * 48, 1000, headroom_bytes=0)["reason"], "compiler_limit")
        self.assertTrue(memory.admission(1, [1] * 47, 1000, headroom_bytes=0)["admitted"])

    def test_admission_rejects_invalid_claims(self):
        for request, claims, available in [(True, [], 100), (0, [], 100), (1, [False], 100), (1, [], 0)]:
            with self.subTest(request=request, claims=claims), self.assertRaises(ValueError):
                memory.admission(request, claims, available)

    def test_unknown_profile_schema_refuses(self):
        p = deepcopy(self.profile())
        p["schema"] = "unknown"
        with self.assertRaises(ValueError):
            memory.module_claim(p, ["Small.v"], self.root, self.compiler)

    def test_weighted_wrapper_uses_declared_helper_in_real_dune_sandbox(self):
        """Run the real wrapper with test data and a fake compiler only."""
        import json
        import os
        import shutil
        import subprocess
        tools = Path(__file__).resolve().parent
        prefix = Path(os.environ.get('OPAM_SWITCH_PREFIX', str(Path.home()/'islaris/_opam')))
        dune = prefix/'bin/dune'
        manifest = (tools/'guard-bin/dune').read_text()
        dependency = '../block/harness/code/admission_memory.py'
        self.assertEqual(manifest.count(dependency), 1)
        names = ['dune_coqc_guarded.sh','dune_coqc_route.sh','resource_guard.sh','coqc_findlib.py',
                 'module_memory.py','run_registry.py','det/coqc_slots.py',
                 'block/harness/code/admission_memory.py','block/harness/code/shell_archive.py','block/harness/code/ledger_archive.py']
        for declared in (True, False):
            with self.subTest(declared=declared):
                workspace = self.root/('declared' if declared else 'missing')
                workspace.mkdir()
                (workspace/'dune-project').write_text('(lang dune 3.7)\n')
                for name in names:
                    target=workspace/'tools'/name
                    target.parent.mkdir(parents=True,exist_ok=True)
                    shutil.copy2(tools/name,target)
                directory=workspace/'tools/guard-bin';directory.mkdir()
                source=directory/'Probe.v';source.write_text('Check nat.\n')
                rule=manifest if declared else manifest.replace(' '+dependency,'')
                rule=rule.replace('../det/coqc_slots.py)', '../det/coqc_slots.py Probe.v)')
                original='(action (copy %{dep:../dune_coqc_guarded.sh} %{target})))'
                action='(action (progn (copy %{dep:../dune_coqc_guarded.sh} %{target}) (run ./coqc Probe.v))))'
                self.assertIn(original,rule)
                (directory/'dune').write_text(rule.replace(original,action))
                fake=workspace/'fake-switch/bin/coqc';fake.parent.mkdir(parents=True)
                fake.write_text('#!/usr/bin/env python3\nimport json,os\n'
                    'with open(os.environ["FAKE_EVENTS"],"a") as f: f.write(json.dumps({"compiler":True})+"\\n")\n')
                fake.chmod(0o755)
                guard=workspace/'tools/resource_guard.sh'
                guard.write_text('#!/usr/bin/env python3\nimport json,os,sys\n'
                    'with open(os.environ["FAKE_EVENTS"],"a") as f: f.write(json.dumps({"claim":int(os.environ["ZESU_MODULE_CLAIM_BYTES"]),"fence":os.environ["ZESU_MODULE_LIMIT_GIB"]})+"\\n")\n'
                    'args=sys.argv[sys.argv.index("--")+1:];os.execv(args[0],args)\n')
                guard.chmod(0o755)
                profile=workspace/'profile.json'
                measured_peak=600*1024**2
                memory.record_measurement(profile,*memory.binding(['Probe.v'],directory,fake),measured_peak)
                events=workspace/'events.jsonl'
                env={k:v for k,v in os.environ.items() if not k.startswith('ZESU_')}
                env.update(PATH=str(prefix/'bin')+os.pathsep+env.get('PATH',''),
                    OPAM_SWITCH_PREFIX=str(fake.parent.parent),OCAMLPATH='',PYTHONPATH='',
                    FAKE_EVENTS=str(events),ZESU_RESOURCE_GUARD=str(guard),
                    ZESU_MODULE_MEMORY_PROFILE=str(profile),ZESU_GATE_MODULE_LIMIT_GIB='16',
                    ZESU_MODULE_MEMORY_OBSERVATIONS=str(workspace/'observations.jsonl'))
                result=subprocess.run([str(dune),'build','--sandbox=copy','--cache=disabled','tools/guard-bin/coqc'],
                    cwd=workspace,env=env,capture_output=True,text=True)
                if declared:
                    self.assertEqual(result.returncode,0,result.stderr)
                    rows=[json.loads(line) for line in events.read_text().splitlines()]
                    claim=memory.booking(measured_peak,16*memory.GIB)
                    self.assertEqual(rows,[{'claim':claim,'fence':'16'},{'compiler':True}])
                    measured=json.loads((workspace/'observations.jsonl').read_text())
                    self.assertEqual((measured['source'],measured['claim_bytes'],measured['claim_reason']),
                                     ('Probe.v',claim,'measured_module'))
                    # A run outside a named guard scope supplies no peak.
                    self.assertIsNone(measured['peak_bytes'])
                    self.assertEqual(memory.load_profile(profile)['modules']['Probe.v']['observations'],1)
                else:
                    self.assertNotEqual(result.returncode,0)
                    self.assertIn('owned admission dependency',result.stderr)
                    self.assertFalse(events.exists())

    def test_build_copy_release_requires_the_archive_dependency(self):
        """Execute the release CLI inside Dune's real copy sandbox."""
        import json
        import os
        import shutil
        import subprocess
        import sys
        tools = Path(__file__).resolve().parent
        sys.path.insert(0, str(tools/'block/harness'))
        import test_unified_admission as fixtures
        dune = Path.home()/'islaris/_opam/bin/dune'
        dependency = '../block/harness/code/shell_archive.py'
        manifest = (tools/'guard-bin/dune').read_text()
        self.assertEqual(manifest.count(dependency), 1)
        for declared in (True, False):
            with self.subTest(declared=declared):
                fixture = fixtures.UnifiedAdmission()
                fixture.setUp()
                try:
                    fixture.confirm()
                    before = fixture.ledger.read_bytes()
                    workspace = self.root/('release-declared' if declared else 'release-missing')
                    workspace.mkdir()
                    (workspace/'dune-project').write_text('(lang dune 3.7)\n')
                    names = ['dune_coqc_guarded.sh', 'dune_coqc_route.sh', 'resource_guard.sh', 'coqc_findlib.py',
                             'module_memory.py', 'run_registry.py', 'det/coqc_slots.py',
                             'block/harness/code/admission_memory.py', 'block/harness/code/shell_archive.py', 'block/harness/code/ledger_archive.py']
                    for name in names:
                        target = workspace/'tools'/name
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(tools/name, target)
                    control = workspace/'tools/ReleaseControl.py'
                    control.write_text("import os,sys\nfrom pathlib import Path\n"
                        "sys.path.insert(0,str(Path(__file__).resolve().parent))\n"
                        "import module_memory as m\n"
                        "reader=m.ScopeReader(proc=Path(os.environ['FIXTURE_PROC']),cgroup_root=Path(os.environ['FIXTURE_CGROUP']))\n"
                        "release=m.release_shell\n"
                        "m.release_shell=lambda marker:release(marker,reader=reader)\n"
                        "sys.argv=['module_memory.py','ledger-release','--marker',os.environ['FIXTURE_MARKER']]\n"
                        "raise SystemExit(m.main())\n")
                    directory = workspace/'tools/guard-bin'
                    directory.mkdir()
                    rule = manifest if declared else manifest.replace(' '+dependency, '')
                    rule = rule.replace('../det/coqc_slots.py)', '../det/coqc_slots.py ../ReleaseControl.py)')
                    rule = rule.replace('(action (copy %{dep:../dune_coqc_guarded.sh} %{target})))',
                        '(action (progn (copy %{dep:../dune_coqc_guarded.sh} %{target}) (run python3 ../ReleaseControl.py))))')
                    (directory/'dune').write_text(rule)
                    environment = dict(os.environ, ZESU_CANONICAL_LEDGER=str(fixture.ledger),
                        FIXTURE_PROC=str(fixture.proc), FIXTURE_CGROUP=str(fixture.reader.root),
                        FIXTURE_MARKER=str(fixture.marker), PYTHONPATH='',
                        PATH=str(dune.parent)+os.pathsep+os.environ.get('PATH', ''))
                    result = subprocess.run([str(dune), 'build', '--sandbox=copy', '--cache=disabled',
                        'tools/guard-bin/coqc'], cwd=workspace, env=environment, capture_output=True, text=True)
                    if declared:
                        self.assertEqual(result.returncode, 0, result.stderr)
                        data = fixture.read()
                        key = fixtures.M.shell_key(fixture.marker)
                        self.assertEqual(data['fixed_claims'][key], 0)
                        self.assertIn(key, data['shell_archive'])
                        self.assertFalse(fixture.marker.exists())
                    else:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn("No module named 'shell_archive'", result.stderr)
                        self.assertEqual(fixture.ledger.read_bytes(), before)
                        self.assertTrue(fixture.marker.exists())
                finally:
                    fixture.tearDown()
                    fixture.doCleanups()

    def physical(self, pid, peak=2 * 1024 ** 2, children=""):
        proc = self.root / "proc"
        process = proc / str(pid)
        (process / "task" / str(pid)).mkdir(parents=True)
        (process / "comm").write_text("coqc\n")
        (process / "exe").symlink_to(self.compiler)
        (process / "status").write_text(f"VmHWM:\t{peak} kB\n")
        (process / "task" / str(pid) / "children").write_text(children)
        return proc

    def marker(self, contents):
        marker = self.root / "reservation"
        marker.write_text(contents)
        return marker

    def test_growth_updates_claims_without_reducing_or_losing_metadata(self):
        proc = self.physical(123)
        marker = self.marker(f"123\nwriter=fixture\naggregate=test\nmemory_claim_bytes={memory.GIB}\n"
                             f"memory_fence_bytes={16 * memory.GIB}\n")
        stamp = marker.stat().st_mtime_ns
        result = memory.reservation_claims([marker], proc=proc, refresh=True)
        self.assertEqual(result["claims"], [3 * memory.GIB])
        self.assertEqual(len(result["growth"]), 1)
        self.assertIn("writer=fixture\naggregate=test\n", marker.read_text())
        self.assertEqual(marker.stat().st_mtime_ns, stamp)
        retained={str(marker):result["claims"][0]}
        (proc / "123/status").write_text("VmHWM:\t1 kB\n")
        result = memory.reservation_claims([marker], proc=proc, refresh=True, retained_claims=retained)
        self.assertEqual(result["claims"], [3 * memory.GIB])
        self.assertEqual(result["growth"], [])

    def test_unrepresented_compilers_keep_full_fallback_reservations(self):
        proc = self.physical(123)
        result = memory.reservation_claims([], proc=proc)
        self.assertEqual(result["claims"], [64 * memory.GIB])
        self.assertEqual(result["unrepresented_compilers"], [123])

    def test_unknown_compiler_cannot_inherit_a_smaller_request_fence(self):
        proc = self.physical(123)
        self.assertEqual(memory.reservation_claims([], proc=proc, fallback_bytes=16*memory.GIB)["claims"],
                         [64*memory.GIB])

    def test_missing_physical_sample_uses_its_fence(self):
        proc = self.physical(123)
        (proc / "123/status").unlink()
        marker = self.marker(f"123\nwriter=\naggregate=\nmemory_claim_bytes={memory.GIB}\n"
                             f"memory_fence_bytes={16 * memory.GIB}\n")
        self.assertEqual(memory.reservation_claims([marker], proc=proc)["claims"], [16 * memory.GIB])

    def test_compiler_that_exits_after_the_snapshot_does_not_grow_its_booking(self):
        import shutil
        proc = self.physical(123)
        marker = self.marker(f"123\nwriter=\naggregate=\nmemory_claim_bytes={memory.GIB}\n"
                             f"memory_fence_bytes={16 * memory.GIB}\n")
        real = memory.compiler_pids

        def snapshot_then_exit(root):
            pids = real(root)
            shutil.rmtree(root / "123")
            return pids
        with patch.object(memory, "compiler_pids", snapshot_then_exit):
            observed = memory.reservation_claims([marker], proc=proc)
        self.assertEqual((observed["claims"], observed["growth"]), ([memory.GIB], []))

    def test_zombie_compiler_does_not_grow_its_booking(self):
        proc = self.physical(123)
        (proc / "123/status").write_text("State:\tZ (zombie)\n")
        marker = self.marker(f"123\nwriter=\naggregate=\nmemory_claim_bytes={memory.GIB}\n"
                             f"memory_fence_bytes={16 * memory.GIB}\n")
        observed = memory.reservation_claims([marker], proc=proc)
        self.assertEqual((observed["claims"], observed["growth"]), ([memory.GIB], []))

    def test_unverified_growth_holds_the_launch_instead_of_failing(self):
        from contextlib import redirect_stdout
        import io
        ledger = self.root / "LEDGER.json"
        ledger.write_text('{"fixed_claims": {}, "region_claims": {}}\n')
        growth = {"claims": [memory.GIB], "growth": [{"reservation": "x", "claim_bytes": 2}],
                  "unrepresented_compilers": []}
        output = io.StringIO()
        with patch("sys.argv", ["module_memory.py", "admission", "--request-bytes", "1",
                               "--available-bytes", "1000000000000"]), \
                patch.object(memory, "reservation_claims", return_value=growth), \
                patch.object(memory, "refresh_shell_growth",
                             side_effect=ValueError("Growth lacks an authenticated shell token.")), \
                patch.object(memory, "current_projection", return_value={"fits": True}), \
                patch.object(memory, "read_shell_bookings", return_value={}), \
                patch.dict(memory.os.environ, {"ZESU_CANONICAL_LEDGER": str(ledger),
                                             "ZESU_GATE_LOCK": str(self.root / "gate.lock")}), \
                redirect_stdout(output):
            self.assertEqual(memory.main(), 0)
        # A non-empty report makes the guard hold and retry; exit 0 never fails the compile.
        self.assertIn("unverified_growth", output.getvalue())
        self.assertIn("authenticated shell token", output.getvalue())

    def test_old_and_probe_reservations_keep_conservative_fences(self):
        proc = self.root / "proc"
        proc.mkdir()
        for extra, expected in [("", 64), ("memory_gib=64\n", 64)]:
            with self.subTest(extra=extra):
                marker = self.marker("confirmed\nwriter=\naggregate=\n" + extra)
                self.assertEqual(memory.reservation_claims([marker], proc=proc)["claims"], [expected * memory.GIB])

    def test_duplicate_or_invalid_retained_memory_refuses(self):
        proc = self.root / "proc"
        proc.mkdir()
        for extra in ("memory_claim_bytes=1\nmemory_claim_bytes=2\n", "memory_claim_bytes=0\n"):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                memory.reservation_claims([self.marker("confirmed\n" + extra)], proc=proc)

    def test_all_physical_children_count_once(self):
        proc = self.physical(123, children="124")
        self.physical(124)
        marker = self.marker(f"123\nwriter=\naggregate=\nmemory_claim_bytes={memory.GIB}\n")
        result = memory.reservation_claims([marker], proc=proc)
        self.assertEqual(result["claims"], [64 * memory.GIB])
        self.assertEqual(result["unrepresented_compilers"], [])

    def identity(self, proc, pid, parent, ticks, state="S"):
        process = proc / str(pid)
        (process / "task" / str(pid)).mkdir(parents=True, exist_ok=True)
        (process / "stat").write_text(f"{pid} (fixture) " + " ".join([state, str(parent)] + ["0"] * 17 + [str(ticks)]))
        children = process / "task" / str(pid) / "children"
        if not children.exists():
            children.write_text("")

    def live_probe(self, peak=2 * 1024 ** 2):
        proc = self.physical(123, peak=peak)
        self.identity(proc, 111, 1, 100)
        self.identity(proc, 122, 111, 200)
        self.identity(proc, 123, 122, 300)
        (proc / "122/task/122/children").write_text("123")
        marker = self.root / "111.1.1"
        marker.write_text("122\nwriter=probe\nprobe=issue10\nmemory_gib=64\ncpu=unlimited\nowner_start=100\n")
        return proc, marker

    def test_live_probe_keeps_full_physical_fence_despite_small_partial_peak(self):
        proc, marker = self.live_probe(peak=3)
        result = memory.reservation_claims([marker], proc=proc, refresh=True)
        self.assertEqual(result["claims"], [64 * memory.GIB])
        self.assertEqual(result["unrepresented_compilers"], [])
        self.assertIn("memory_gib=64\n", marker.read_text())
        self.assertNotIn("memory_probe_child_start=", marker.read_text())
        self.assertNotIn("memory_fence_bytes=", marker.read_text())

    def test_live_probe_never_reduces_the_full_fence_claim(self):
        proc, marker = self.live_probe()
        stamp = marker.stat().st_mtime_ns
        self.assertEqual(memory.reservation_claims([marker], proc=proc, refresh=True)["claims"], [64 * memory.GIB])
        (proc / "123/status").write_text(f"VmHWM: {4 * 1024 ** 2} kB\n")
        self.assertEqual(memory.reservation_claims([marker], proc=proc, refresh=True)["claims"], [64 * memory.GIB])
        (proc / "123/status").write_text("VmHWM: 1 kB\n")
        self.assertEqual(memory.reservation_claims([marker], proc=proc, refresh=True)["claims"], [64 * memory.GIB])
        self.assertEqual(marker.stat().st_mtime_ns, stamp)
        self.assertIn("memory_gib=64\n", marker.read_text())

    def test_probe_owner_reuse_cannot_supply_a_small_claim(self):
        proc, marker = self.live_probe()
        self.identity(proc, 111, 1, 101)
        result = memory.reservation_claims([marker], proc=proc)
        self.assertGreaterEqual(sum(result["claims"]), 64 * memory.GIB)
        self.assertEqual(result["unrepresented_compilers"], [123])

    def test_probe_collector_reuse_refuses_retained_identity(self):
        proc, marker = self.live_probe()
        memory.reservation_claims([marker], proc=proc, refresh=True)
        self.identity(proc, 122, 111, 201)
        self.assertGreaterEqual(sum(memory.reservation_claims([marker], proc=proc)["claims"]), 64 * memory.GIB)

    def test_probe_unrelated_child_cannot_supply_a_small_claim(self):
        proc, marker = self.live_probe()
        self.identity(proc, 122, 999, 200)
        self.assertGreaterEqual(sum(memory.reservation_claims([marker], proc=proc)["claims"]), 64 * memory.GIB)

    def test_probe_zombie_or_missing_sample_keeps_fence_fallback(self):
        for zombie in [True, False]:
            with self.subTest(zombie=zombie):
                proc, marker = self.live_probe()
                if zombie:
                    self.identity(proc, 123, 122, 300, state="Z")
                else:
                    (proc / "123/status").unlink()
                self.assertGreaterEqual(sum(memory.reservation_claims([marker], proc=proc)["claims"]), 64 * memory.GIB)
                for directory in sorted(proc.rglob("*"), reverse=True):
                    if directory.is_symlink() or directory.is_file():
                        directory.unlink()
                    elif directory.is_dir():
                        directory.rmdir()
                proc.rmdir()

    def test_probe_identity_change_during_measurement_refuses_small_claim(self):
        proc, marker = self.live_probe()
        original = memory.process_identity
        count = 0
        def changing(root, pid):
            nonlocal count
            found = original(root, pid)
            if pid == 123:
                count += 1
                if count > 1:
                    return (122, "301")
            return found
        with patch.object(memory, "process_identity", changing):
            self.assertGreaterEqual(sum(memory.reservation_claims([marker], proc=proc)["claims"]), 64 * memory.GIB)

    def test_probe_collector_reuse_between_identity_reads_refuses(self):
        proc, marker = self.live_probe()
        original = memory.process_identity
        reads = 0
        def changing(root, pid):
            nonlocal reads
            found = original(root, pid)
            if pid == 122:
                reads += 1
                if reads > 1:
                    return (111, "201")
            return found
        with patch.object(memory, "process_identity", changing):
            self.assertGreaterEqual(sum(memory.reservation_claims([marker], proc=proc)["claims"]), 64 * memory.GIB)

    def test_probe_multiple_physical_children_count_once(self):
        proc, marker = self.live_probe()
        self.physical(124)
        self.identity(proc, 124, 122, 301)
        (proc / "122/task/122/children").write_text("123 124")
        self.assertEqual(memory.reservation_claims([marker], proc=proc)["claims"], [64 * memory.GIB])

    def measured_probe(self, proc, marker):
        with marker.open('a') as stream:
            stream.write(f'memory_claim_bytes={8 * memory.GIB}\nmemory_fence_bytes={64 * memory.GIB}\n')
        return {str(marker): 8 * memory.GIB}

    def test_authorized_measured_pet_probe_keeps_claim_without_coqc(self):
        proc, marker = self.live_probe()
        retained = self.measured_probe(proc, marker)
        (proc/'123/comm').write_text('python\n')
        with patch.object(memory, 'authorized_shell_booking', return_value=8 * memory.GIB) as authorize:
            result = memory.reservation_claims([marker], proc=proc, retained_claims=retained)
        self.assertEqual(result['claims'], [8 * memory.GIB])
        self.assertEqual(result['unrepresented_compilers'], [])
        authorize.assert_called_once_with(marker, 8 * memory.GIB)
        self.assertEqual(result['growth'], [])

    def test_unauthorized_measured_pet_probe_retains_fence(self):
        proc, marker = self.live_probe()
        retained = self.measured_probe(proc, marker)
        (proc/'123/comm').write_text('python\n')
        with patch.object(memory, 'authorized_shell_booking', return_value=None):
            result = memory.reservation_claims([marker], proc=proc, retained_claims=retained)
        self.assertEqual(result['claims'], [64 * memory.GIB])

    def test_authorized_probe_growth_never_reduces_recorded_booking(self):
        proc, marker = self.live_probe(peak=8 * 1024 ** 2)
        retained = self.measured_probe(proc, marker)
        before = marker.read_bytes()
        with patch.object(memory, 'authorized_shell_booking', return_value=8 * memory.GIB):
            result = memory.reservation_claims([marker], proc=proc, retained_claims=retained)
        self.assertEqual(result['claims'], [12 * memory.GIB])
        self.assertEqual(result['growth'][0]['previous_bytes'], 8 * memory.GIB)
        self.assertEqual(marker.read_bytes(), before)

    def test_probe_conflicting_physical_fence_refuses(self):
        proc, marker = self.live_probe()
        with marker.open("a") as stream:
            stream.write(f"memory_fence_bytes={16 * memory.GIB}\n")
        with self.assertRaisesRegex(ValueError, "physical policy"):
            memory.reservation_claims([marker], proc=proc)

    def test_live_probe_legacy_small_claim_cannot_reduce_the_fence(self):
        proc, marker = self.live_probe()
        with marker.open("a") as stream:
            stream.write(f"memory_claim_bytes={64 * memory.GIB}\n")
        self.assertEqual(memory.reservation_claims([marker], proc=proc)["claims"], [64 * memory.GIB])

    def test_probe_refresh_false_preserves_marker(self):
        proc, marker = self.live_probe()
        before = marker.read_bytes()
        self.assertEqual(memory.reservation_claims([marker], proc=proc)["claims"], [64 * memory.GIB])
        self.assertEqual(marker.read_bytes(), before)


class AdmissionTotalsTests(unittest.TestCase):
    """Ledger writers publish totals that wake held launches."""

    def test_confirm_publishes_and_release_subtracts(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "admission-summary"
            result = {"fits": True, "requested_total_bytes": 10, "requested_unrealized_bytes": 8,
                      "accounted_active_bytes": 7, "unrealized_claim_bytes": 6, "budget_bytes": 100,
                      "slice_claim_cap_bytes": 90, "slice_max_bytes": 175,
                      "live_memory_sample": {"live_bytes": 4}}
            self.assertEqual(memory.publish_admission_totals(result, path=path), [10, 8, 100, 90, 4, 175])
            self.assertEqual(memory.publish_admission_totals(released_bytes=3, path=path), [7, 5, 100, 90, 4, 175])
            self.assertEqual(path.read_text().split(), ["7", "5", "100", "90", "4", "175"])
            refused = dict(result, fits=False)
            del refused["live_memory_sample"]
            self.assertEqual(memory.publish_admission_totals(refused, path=path), [7, 6, 100, 90, -1, 175])
            self.assertIsNone(memory.publish_admission_totals(result))


class GateProfileTests(unittest.TestCase):
    """Every guarded compile books from the shared profile and measures itself."""

    def setUp(self):
        import json, sys
        self.json, self.sys = json, sys
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.compiler = self.root / "coqc"
        self.compiler.write_text("#!/usr/bin/env python3\nimport os, sys\n"
                                 "b = bytearray(int(os.environ.get('FAKE_MIB', '1')) * 1024 * 1024)\n"
                                 "b[::4096] = b'1' * len(b[::4096])\n"
                                 "sys.exit(int(os.environ.get('FAKE_STATUS', '0')))\n")
        self.compiler.chmod(0o755)
        (self.root / "Measured.v").write_text("Check nat.\n")
        (self.root / "Unmeasured.v").write_text("Check bool.\n")
        self.observations = self.root / "observations.jsonl"
        self.profile_path = self.root / "cache" / "profile.json"
        self.claims = self.root / "claims.txt"
        # The fake guard names the test's own cgroup as its scope, as
        # scope-exec does for the real systemd scope, and records the claim.
        self.guard = self.root / "guard.py"
        self.guard.write_text(
            "#!/usr/bin/env python3\nimport os, pathlib, sys\n"
            "with open(os.environ['FAKE_CLAIMS'], 'a') as f: f.write(os.environ['ZESU_MODULE_CLAIM_BYTES'] + '\\n')\n"
            "leaf = next(l for l in open('/proc/self/cgroup') if l.startswith('0::')).split(':', 2)[2].strip()\n"
            "os.environ['ZESU_SCOPE_UNIT'] = pathlib.PurePosixPath(leaf).name\n"
            "args = sys.argv[sys.argv.index('--') + 1:]\nos.execv(args[0], args)\n")
        self.guard.chmod(0o755)

    def run_observed(self, source, megabytes, status=0):
        environment = {"FAKE_MIB": str(megabytes), "FAKE_STATUS": str(status), "FAKE_CLAIMS": str(self.claims)}
        with patch("signal.signal"), patch.dict(memory.os.environ, environment):
            return memory.observe(self.profile_path, self.observations, self.guard, self.compiler,
                                  self.root, ["-q", source], fallback_bytes=16 * memory.GIB)

    def rows(self):
        return [self.json.loads(line) for line in self.observations.read_text().splitlines()]

    def test_clean_compile_records_its_scope_peak_and_the_next_compile_books_it(self):
        self.assertEqual(self.run_observed("Measured.v", 64), 0)
        first = self.rows()[-1]
        self.assertEqual((first["claim_bytes"], first["claim_reason"]), (16 * memory.GIB, "unknown_module"))
        self.assertGreater(first["peak_bytes"], 0)
        row = memory.load_profile(self.profile_path)["modules"]["Measured.v"]
        self.assertEqual(row["peak_bytes"], first["peak_bytes"])
        self.assertEqual(self.run_observed("Measured.v", 1), 0)
        second = self.rows()[-1]
        self.assertEqual(second["claim_reason"], "measured_module")
        self.assertEqual(second["claim_bytes"], memory.booking(first["peak_bytes"], 16 * memory.GIB))
        self.assertEqual(self.claims.read_text().split(), [str(16 * memory.GIB), str(second["claim_bytes"])])
        self.assertLessEqual(first["admitted_ns"], first["ended_ns"])
        # Harness CPU is the guarded CPU less the compiler's own CPU.
        self.assertGreaterEqual(first["guarded_cpu_seconds"], first["compiler_cpu_seconds"])
        self.assertGreater(first["compiler_cpu_seconds"], 0)

    def test_failed_compile_records_nothing_and_keeps_its_status(self):
        self.assertEqual(self.run_observed("Unmeasured.v", 1, status=3), 3)
        self.assertFalse(self.observations.exists())
        self.assertEqual(memory.load_profile(self.profile_path)["modules"], {})

    def test_compile_outside_a_named_scope_supplies_no_peak(self):
        self.guard.write_text("#!/usr/bin/env python3\nimport os, sys\n"
                              "os.environ.pop('ZESU_SCOPE_UNIT', None)\n"
                              "args = sys.argv[sys.argv.index('--') + 1:]\nos.execv(args[0], args)\n")
        self.assertEqual(self.run_observed("Measured.v", 1), 0)
        self.assertIsNone(self.rows()[-1]["peak_bytes"])
        self.assertEqual(memory.load_profile(self.profile_path)["modules"], {})

    def test_summary_counts_bookings_from_admission_to_exit(self):
        with self.observations.open("w") as stream:
            for start, admitted, end, reason in ((0, 0, 10, "measured_module"), (0, 5, 15, "measured_module"),
                                                 (0, 12, 30, "unknown_module")):
                stream.write(self.json.dumps({"claim_bytes": memory.GIB, "started_ns": start,
                                              "admitted_ns": admitted, "ended_ns": end,
                                              "peak_bytes": memory.GIB // 2, "claim_reason": reason}) + "\n")
        summary = memory.booked_versus_peak(self.observations)
        self.assertEqual(summary["maximum_concurrent_booked_bytes"], 2 * memory.GIB)
        self.assertEqual(summary["maximum_concurrent_peak_bytes"], memory.GIB)
        self.assertEqual((summary["compiles"], summary["unmeasured_fence_bookings"]), (3, 1))
        self.assertEqual(summary["peak_bytes_max"], memory.GIB // 2)

    def test_summary_counts_directory_priors_apart_from_fence_bookings(self):
        with self.observations.open("w") as stream:
            for reason in ("unknown_module", "directory_prior", "measured_module"):
                stream.write(self.json.dumps({"claim_bytes": memory.GIB, "claim_reason": reason}) + "\n")
        summary = memory.booked_versus_peak(self.observations)
        self.assertEqual((summary["unmeasured_fence_bookings"], summary["directory_prior_bookings"]), (1, 1))


if __name__ == "__main__":
    unittest.main()
