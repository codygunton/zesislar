import importlib.util,unittest,tempfile,hashlib
from pathlib import Path
P=Path(__file__).resolve().parent / 'block'
spec=importlib.util.spec_from_file_location('backend172',P/'trace_block_mcp.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class ResidualTrials(unittest.TestCase):
 def test_absent_preserves_legacy(self):self.assertEqual(m.validated_residual_trials({}),[])
 def test_exact_binding(self):
  with tempfile.TemporaryDirectory() as root:
   source=Path(root)/'source.v';source.write_text('Ltac unchanged := idtac.')
   command='all: idtac.'
   trial=dict(name='whole-rule',rule='FinishFacts',exposure='not-exposed',command=command,command_sha256=hashlib.sha256(command.encode()).hexdigest(),sources=[dict(path=str(source),sha256=hashlib.sha256(source.read_bytes()).hexdigest())])
   request=dict(observer_runtime={},residual_trials=[trial]);self.assertEqual(m.validated_residual_trials(request),[trial])
   trial['command_sha256']='0'*64
   with self.assertRaises(ValueError):m.validated_residual_trials(request)
 def test_sources_bound_before_manifest(self):
  source=(P/'trace_block_mcp.py').read_text()
  self.assertLess(source.index('for trial in residual_trials:'),source.index('evidence_dir / "RUN-MANIFEST.json"'))
 def test_residual_focus_is_explicit(self):
  source=(P/'trace_block_mcp.py').read_text()
  self.assertIn("'1: ltac2:(trace_block_snapshot",source)
  self.assertIn('"selected_goal_id": goal',source)
  self.assertIn('"hidden_peer_goals": {"availability": "unavailable"',source)
 def test_only_supported_full_label(self):
  source=(P/'trace_block_mcp.py').read_text()
  self.assertNotIn('residual-hand-before-',source)
  self.assertIn('event_paths() - previous',source)
  self.assertIn('The residual trial has no full before checkpoint.',source)
  self.assertIn('The residual trial has no full rollback checkpoint.',source)
 def test_chunk_identity_matches_producer(self):
  source=(P/'trace_block_mcp.py').read_text()
  self.assertIn('logical = "event-%08d/capture"',source)
 def test_requires_filtered(self):
  with self.assertRaises(ValueError):m.validated_residual_trials(dict(residual_trials=[{}]))
 def test_rejects_unknown_rule(self):
  with self.assertRaises(ValueError):m.validated_residual_trials(dict(observer_runtime={},residual_trials=[dict(rule='Other')]))
if __name__=='__main__':unittest.main()
