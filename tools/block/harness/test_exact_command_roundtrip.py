"""Exercise the exact launcher's real pre-admission equality boundary."""
import ast
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

DIRECTORY = Path('/home/cody/zesislar/_build/agents/worker-build-2/join-automation-0d2-v1/control-Lithium-resource023-shared-wrap')
LAUNCHER = DIRECTORY / 'LAUNCH-PUBLIC-EXACT-v2.py'

@unittest.skipUnless(LAUNCHER.exists(), 'The released local control fixture is absent.')
class CommandRoundtripTests(unittest.TestCase):
 def prefix(self):
  self.assertEqual(hashlib.sha256(LAUNCHER.read_bytes()).hexdigest(),'43d370964c1f64b862d92b4f5e307fedb6f99699187be7a3a2256f227649643b')
  tree=ast.parse(LAUNCHER.read_text());nodes=[]
  for node in tree.body:
   nodes.append(node)
   if isinstance(node,ast.Assert) and ast.unparse(node.test)=='validated == c':break
  else:self.fail('The real pre-admission equality assertion is absent.')
  return compile(ast.Module(body=nodes,type_ignores=[]),str(LAUNCHER),'exec')
 def run_boundary(self, command):
  with tempfile.TemporaryDirectory() as temporary:
   path=Path(temporary)/'COMMAND.json';path.write_text(json.dumps(command)+'\n')
   digest=hashlib.sha256(path.read_bytes()).hexdigest()
   with patch.object(sys,'argv',[str(LAUNCHER),str(path),digest]):
    exec(self.prefix(),{'__name__':'actual_pre_admission_boundary'})
 def test_canonical_command_equals_actual_validator_output(self):
  self.run_boundary(json.loads((DIRECTORY/'PUBLIC-PREDECESSOR-COMMAND-v7.json').read_text()))
 def test_out_of_band_metadata_still_refuses(self):
  command=json.loads((DIRECTORY/'PUBLIC-PREDECESSOR-COMMAND-v7.json').read_text())
  command['experiment']='selector-under-actual-bound-bank'
  with self.assertRaises(AssertionError):self.run_boundary(command)

if __name__=='__main__':unittest.main()
