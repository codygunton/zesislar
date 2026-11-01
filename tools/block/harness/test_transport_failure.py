import json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import scratch
from transport_mapping import audit

class TransportFailureControls(unittest.TestCase):
 def test_actual_provider_and_resource_audits(self):
  for name in ['entry_chain_provider.py','entry_chain_resources.py']:
   report=audit(scratch.HERE/'code'/name)
   expected='check_operation' if name=='entry_chain_provider.py' else 'check_proof_bindings'
   self.assertIn(expected,[r['sink'] for r in report['reviewed_sinks']])
 def test_unknown_sink_still_refuses(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d)/'bad.py';p.write_text('unreviewed(runtime)\n')
   with self.assertRaisesRegex(ValueError,'escapes'):audit(p)
 def test_unknown_field_still_refuses(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d)/'bad.py';p.write_text('value=runtime["unknown"]\n')
   with self.assertRaisesRegex(ValueError,'typed mapping'):audit(p)
 def test_first_error_survives_absent_lifecycle_receipts(self):
  with tempfile.TemporaryDirectory() as d:
   out=Path(d);native=out/'native-job';native.mkdir()
   c={'bindings':[],'jobs':[{'key':'prerequisites','ordered_modules':[],'output':str(out/'pre')},{'key':'800d6a64','output':str(native)}],'job_controller':{'path':'unused-controller'}}
   path=out/'RUNTIME.json';path.write_text(json.dumps(c));(out/'INPUTS.json').write_text('{}')
   first='A runtime value escapes the audited consumers.'
   result=native/'RESULT.json';result.write_text(json.dumps({'status':'infrastructure_failed','error':first,'last_phase':'cache_or_prospective_collection'}));before=scratch.digest(result)
   with patch('restart_bindings.verify_restart_runtime'),patch.object(scratch,'check_proof_bindings'),patch.object(scratch.subprocess,'run'):
    self.assertEqual(scratch.execute(path,scratch.digest(path)),2)
   public=json.loads((out/'RESULT.json').read_text())
   self.assertEqual(public['first_error'],first)
   self.assertEqual(public['lifecycle_receipts_unavailable'],['closure','release'])
   self.assertEqual(scratch.digest(result),before)
 def test_sealed_native_uses_original_runtime_without_READY_copy(self):
  with tempfile.TemporaryDirectory() as d:
   out=Path(d);native=out/'native-job';native.mkdir();ready=out/'READINESS.json';ready.write_text('{"objects":[]}')
   c={'bindings':[],'jobs':[{'key':'prerequisites','ordered_modules':[],'output':str(out/'pre')},{'key':'800d6a64','output':str(native)}],
      'job_controller':{'path':'unused-controller'},'sealed_native_preparation':{'job':'800d6a64'},'readiness':scratch.binding(ready)}
   path=out/'RUNTIME.json';path.write_text(json.dumps(c));before=scratch.digest(path);(out/'INPUTS.json').write_text('{}')
   (native/'RESULT.json').write_text(json.dumps({'status':'infrastructure_failed','error':'retained diagnostic failure'}))
   with patch('restart_bindings.verify_restart_runtime'),patch.object(scratch,'check_proof_bindings'),patch.object(scratch.subprocess,'run') as run:
    self.assertEqual(scratch.execute(path,before),2)
   self.assertEqual(scratch.digest(path),before);self.assertFalse((out/'READY-RUNTIME.json').exists())
   self.assertEqual(run.call_args.args[0][3],str(path));self.assertEqual(json.loads((out/'RESULT.json').read_text())['runtime'],scratch.binding(path))
if __name__=='__main__':unittest.main()
