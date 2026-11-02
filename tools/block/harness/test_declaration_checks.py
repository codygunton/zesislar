import json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import scratch

class DeclarationChecks(unittest.TestCase):
 def invoke(self, returned):
  with tempfile.TemporaryDirectory() as d:
   out=Path(d);pre=out/"pre";(pre/"native").mkdir(parents=True)
   specification={"problem_name":"one","proof":"exact proof","problem_statement":"exact statement"}
   c={"bindings":[],"jobs":[{"key":"prerequisites","ordered_modules":[],"output":str(pre)},{"key":"native"}],"declaration_checks":[specification],"declarations_only":True,"adoption_implementation":{"path":"unused"},"job_controller":{"path":"controller"},"source_overrides":[]}
   source=out/'Carrier.v';source.write_text('(* nonproof carrier fixture *)\n')
   target={'module':'Fixture.Carrier','source_sha256':scratch.digest(source)}
   c.update(prepared_workspace=str(out),proof_runtime={'module_files':{'Fixture.Carrier':'Carrier.v'}})
   c['jobs'][0].update(phase='prerequisites',target=target)
   c['jobs'][1].update(phase='native',target=target)
   path=out/"RUNTIME.json";path.write_text(json.dumps(c));(pre/"RESULT.json").write_text(json.dumps({"success":True}));(out/"READINESS.json").write_text(json.dumps({"objects":[]}))
   rows=returned(specification)
   for row in rows:row['result'].setdefault('success',True)
   (pre/"native/CONTROL-VERIFICATION.json").write_text(json.dumps(rows))
   with patch("restart_bindings.verify_restart_runtime"),patch.object(scratch,"check_proof_bindings"),patch("controller_cleanup.run") as launch,patch("runpy.run_path",return_value={"prerequisite_readiness":lambda *args:None}):
    result=scratch.execute(path,scratch.digest(path))
    self.assertEqual(result,0);self.assertEqual(launch.call_count,1)
    self.assertEqual(launch.call_args.args[0][-2],"prerequisites")
    saved=json.loads((out/"RESULT.json").read_text());self.assertEqual(saved["exact_statement_check_count"],1)
 def test_checks_only_runs_without_recompilation(self):
  self.invoke(lambda s:[{"specification":s,"result":{"verification_method":"module_m","assumptions":[]}}])
 def test_omitted_checks_refuse(self):
  with self.assertRaisesRegex(ValueError,"did not all run"):self.invoke(lambda s:[])
 def test_failed_verification_refuses(self):
  with self.assertRaisesRegex(ValueError,'check failed'):self.invoke(lambda s:[{'specification':s,'result':{'success':False,'verification_method':'module_m','assumptions':[]}}])
 def test_wrong_method_refuses(self):
  with self.assertRaisesRegex(ValueError,"check failed"):self.invoke(lambda s:[{"specification":s,"result":{"verification_method":"other","assumptions":[]}}])
 def test_assumption_refuses(self):
  with self.assertRaisesRegex(ValueError,"check failed"):self.invoke(lambda s:[{"specification":s,"result":{"verification_method":"module_m","assumptions":["axiom"]}}])
if __name__=="__main__":unittest.main()
