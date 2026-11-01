"""Check measured reservations without launching compilers."""

from copy import deepcopy
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

    def observation(self, source="Small.v", peak=600000):
        return {"exe": str(self.compiler), "cwd": str(self.root),
                "command": str(self.compiler) + " -q " + source,
                "observed_peak_rss_kib": peak}

    def profile(self, rows=None):
        return memory.make_profile(rows or [self.observation()], {"exit_code": 0}, self.compiler)

    def test_small_modules_use_the_floor_and_large_modules_use_measured_margin(self):
        p = self.profile([self.observation(), self.observation("Large.v", 8 * 1024 ** 2)])
        self.assertEqual(p["modules"]["Small.v"]["claim_bytes"], memory.GIB)
        self.assertEqual(p["modules"]["Large.v"]["claim_bytes"], 12 * memory.GIB)

    def test_repeated_module_uses_the_largest_measurement(self):
        p = self.profile([self.observation(peak=2 * 1024 ** 2), self.observation(peak=1024 ** 2)])
        self.assertEqual(p["modules"]["Small.v"]["claim_bytes"], 3 * memory.GIB)

    def test_failed_or_incomplete_gate_cannot_supply_measurements(self):
        for result in ({}, {"exit_code": 1}, {"exit_code": False}):
            with self.subTest(result=result), self.assertRaises(ValueError):
                memory.make_profile([self.observation()], result, self.compiler)

    def test_invalid_peaks_refuse(self):
        for peak in (-1, None, True, 1.5):
            with self.subTest(peak=peak), self.assertRaises(ValueError):
                self.profile([self.observation(peak=peak)])

    def test_ambiguous_or_escaping_source_paths_refuse(self):
        for arguments in ([], ["Small.v", "Large.v"], ["../Small.v"], ["/Small.v"], ["./Small.v"]):
            with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                memory.module_source(arguments)

    def test_measured_claim_requires_matching_compiler_and_source(self):
        p = self.profile()
        value = memory.module_claim(p, ["-q", "Small.v"], self.root, self.compiler)
        self.assertEqual((value["claim_bytes"], value["reason"]), (memory.GIB, "measured_module"))
        (self.root / "Small.v").write_text("Check unit.\n")
        self.assertEqual(memory.module_claim(p, ["Small.v"], self.root, self.compiler)["reason"], "changed_source")

    def test_changed_compiler_uses_the_full_fallback(self):
        p = self.profile()
        self.compiler.write_bytes(b"changed")
        value = memory.module_claim(p, ["Small.v"], self.root, self.compiler)
        self.assertEqual((value["claim_bytes"], value["reason"]), (16 * memory.GIB, "changed_compiler"))

    def test_unknown_module_and_missing_peak_use_the_full_fallback(self):
        p = self.profile([self.observation(peak=0)])
        for source, reason in [("Small.v", "missing_peak"), ("Large.v", "unknown_module")]:
            value = memory.module_claim(p, ["-q", source], self.root, self.compiler)
            self.assertEqual((value["claim_bytes"], value["reason"]), (16 * memory.GIB, reason))

    def test_unrecognized_command_uses_the_full_fallback(self):
        value = memory.module_claim(self.profile(), ["Small.v", "Large.v"], self.root, self.compiler)
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

    def test_legacy_profile_without_complete_measurement_keeps_actual_fence(self):
        profile = self.profile()
        profile.pop("measurement_complete")
        result = memory.module_claim(profile, ["-q", "Small.v"], self.root, self.compiler,
                                     fallback_bytes=64 * memory.GIB)
        self.assertEqual((result["claim_bytes"], result["reason"]),
                         (64 * memory.GIB, "incomplete_measurement"))

    def test_changed_compiler_arguments_keep_actual_fence(self):
        result = memory.module_claim(self.profile(), ["-q", "-native-compiler", "no", "Small.v"],
                                     self.root, self.compiler, fallback_bytes=64 * memory.GIB)
        self.assertEqual((result["claim_bytes"], result["reason"]),
                         (64 * memory.GIB, "changed_arguments"))

    def test_admission_cli_passes_the_actual_fence_to_unknown_compilers(self):
        with patch("sys.argv", ["module_memory.py", "admission", "--request-bytes", "1",
                               "--available-bytes", "1000000000000", "--fallback-bytes", str(64*memory.GIB)]), \
                patch.object(memory, "reservation_claims", return_value={"claims": [], "growth": [], "unrepresented_compilers": []}) as observed:
            self.assertEqual(memory.main(), 0)
        self.assertEqual(observed.call_args.kwargs['fallback_bytes'], 64*memory.GIB)

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
        (proc / "123/status").write_text("VmHWM:\t1 kB\n")
        result = memory.reservation_claims([marker], proc=proc, refresh=True)
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
        self.assertIn("memory_probe_child_start=200\n", marker.read_text())
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


if __name__ == "__main__":
    unittest.main()
