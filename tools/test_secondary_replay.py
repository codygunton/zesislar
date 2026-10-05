"""Secondary replay verifies immutable primary evidence and timeout selection."""
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).parent/'block'))
from replay_secondary import jobs


class SecondaryReplayTests(unittest.TestCase):
    def fixture(self, root):
        source = root/'Frozen.v';source.write_text('unchanged primary source')
        capture = source.with_suffix('.mcp.json');capture.write_text('unchanged primary capture')
        index = {str(p): {'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
                 for p in (source, capture)}
        primary = {'blocks': [
            {'entry': '0x10', 'outcomes': ['automation-search-timeout'],
             'secondary_diagnostics': [{'source': str(source)}]},
            {'entry': '0x20', 'outcomes': ['primary-unavailable'], 'secondary_diagnostics': []},
            {'entry': '0x30', 'outcomes': ['reached'], 'secondary_diagnostics': []}]}
        return source, capture, index, primary

    def test_selects_only_recorded_primary_timeouts(self):
        with tempfile.TemporaryDirectory() as temp:
            source, _, index, primary = self.fixture(Path(temp))
            selected = jobs(primary, index)
            self.assertEqual([row['entry'] for row in selected], ['0x10'])
            self.assertEqual(selected[0]['primary_outcomes'], ['automation-search-timeout'])
            self.assertEqual(selected[0]['sources'][0]['path'], str(source))

    def test_changed_primary_source_prevents_any_replay(self):
        with tempfile.TemporaryDirectory() as temp:
            source, _, index, primary = self.fixture(Path(temp));source.write_text('changed')
            with self.assertRaisesRegex(ValueError, 'primary source changed'):
                jobs(primary, index)

    def test_changed_primary_capture_prevents_any_replay(self):
        with tempfile.TemporaryDirectory() as temp:
            _, capture, index, primary = self.fixture(Path(temp));capture.write_text('changed')
            with self.assertRaisesRegex(ValueError, 'primary capture changed'):
                jobs(primary, index)


if __name__ == '__main__':
    unittest.main()
