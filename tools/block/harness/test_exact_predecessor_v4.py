"""Check the released predecessor guard without enabling resource023."""
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch
p=Path(__file__).with_name('exact_predecessor_v4.py')
s=importlib.util.spec_from_file_location('exact_predecessor_v4',p)
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)

class PredecessorGuardTests(unittest.TestCase):
 def setUp(self):
  self.policy=m.read({'path':str(m.POLICY),'sha256':m.POLICY_SHA})
  self.row=self.policy['cases']['predecessor']
  self.output=Path(self.row['spec']['path']).parent/'predecessor004'
 def test_exact_predecessor(self):
  command=m.validate('predecessor',self.output)
  self.assertEqual(command['claim_bytes'],8589934592)
  self.assertEqual(command['physical_fence_bytes'],68719476736)
  self.assertTrue(command['argv'][5].endswith('-v4'))
  self.assertEqual(m.read(command['spec'])['helper']['sha256'],'87a7951c14663a6fa2607b8490c323838f5729a0e56a895ee64e93b0a142704d')
 def test_resource_successor_disabled(self):
  with self.assertRaises(ValueError):m.validate('resource023',self.output)
 def test_changed_helper_refused(self):
  original=m.binding
  def binding(path):
   value=original(path)
   if str(path).endswith('/Rule-v2.vpart'):value['sha256']='0'*64
   return value
  with patch.object(m,'binding',side_effect=binding):
   with self.assertRaises(ValueError):m.validate('predecessor',self.output)

if __name__=='__main__':unittest.main()
