import tempfile,unittest
from pathlib import Path
import scratch
import _test_support
class ControlSessionArguments(unittest.TestCase):
 def args(self,extra):
  entry=_test_support.SOURCE/'workspace/artifacts/default/ZesuSsz/Generated/DecodeItem/Entries.v'
  with tempfile.TemporaryDirectory() as d:return _test_support.arguments(['800d6a08',str(entry),'--output',d+'/attempt','--control-session','/unused/session.json']+extra)
 def test_session_requires_declarations_only(self):
  with self.assertRaises(SystemExit):self.args(['--rules',str(_test_support.SOURCE/'workspace/artifacts/default/ZesuSsz/Generated/DecodeItem/Entries.v')])
 def test_session_requires_rules(self):
  with self.assertRaises(SystemExit):self.args(['--declarations-only'])
 def test_session_refuses_mixed_exact_checks(self):
  entry=str(_test_support.SOURCE/'workspace/artifacts/default/ZesuSsz/Generated/DecodeItem/Entries.v')
  with self.assertRaises(SystemExit):self.args(['--declarations-only','--rules',entry,'--declaration-checks','/unused/checks.json'])
if __name__=='__main__':unittest.main()
