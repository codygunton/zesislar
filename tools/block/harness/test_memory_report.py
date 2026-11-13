import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parent/'code'))
import scratch
import scratch_limits as limits

class MemoryReports(unittest.TestCase):
    def test_more_than_twice_claim_does_not_stop(self):
        self.assertIsNone(limits.stop_reason(1, 500, 2))
    def test_physical_fence_stops(self):
        self.assertEqual(limits.stop_reason(1, limits.MEMORY_FENCE_BYTES, 10**12), 'external_memory_stop')
    def test_below_physical_fence_keeps_running(self):
        self.assertIsNone(limits.stop_reason(1, limits.MEMORY_FENCE_BYTES-1, 2))
    def test_CPU_stop_keeps_7200_limit(self):
        self.assertEqual(limits.stop_reason(7201, 0, 2, origin_cpu=1), 'external_CPU_stop')
    def test_report_threshold_keeps_strict_boundary(self):
        self.assertFalse(limits.claim_report_required(4, 2))
        self.assertTrue(limits.claim_report_required(5, 2))
    def test_report_writes_without_stopping_child(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);out=root/'out';out.mkdir();parent=root/'zesuworkloads.slice';parent.mkdir();(parent/'memory.max').write_text('187904819200');(parent/'memory.swap.max').write_text('0');group=parent/'zesuworkloads-aggregate1p2r3.slice';group.mkdir();(group/'memory.max').write_text(str(limits.MEMORY_FENCE_BYTES));(group/'memory.swap.max').write_text('0')
            (group/'cpu.stat').write_text('usage_usec 1000000\n')
            (group/'memory.current').write_text('5')
            (group/'memory.peak').write_text('6')
            stat=group.stat();identity=dict(aggregate_path=str(group),aggregate_device=stat.st_dev,aggregate_inode=stat.st_ino)
            (out/'BATCH-IDENTITY.json').write_text(json.dumps(identity))
            class Child:
                count=0
                def poll(self):
                    self.count+=1
                    return None if self.count==1 else 0
                def wait(self):return 0
            with patch.object(limits.subprocess,'run') as run, patch.object(limits.time,'sleep'):
                self.assertEqual(limits.wait_with_limits(Child(),out,2),0)
            run.assert_not_called()
            report=json.loads((out/'MEMORY-CLAIM-REPORT.json').read_text())
            self.assertTrue(report['report_only'])
            self.assertFalse(report['proof_search_stopped'])
            self.assertFalse((out/'EXTERNAL-STOP.json').exists())

if __name__=='__main__':unittest.main()
