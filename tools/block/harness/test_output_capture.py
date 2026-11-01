from pathlib import Path
import hashlib,json,os,subprocess,sys,tempfile,unittest
import _historical_fixtures as historical
HERE=Path(__file__).resolve().parent
class OutputCapture(unittest.TestCase):
 def sample(self,code):
  with tempfile.TemporaryDirectory() as name:
   root=Path(name);directory=root/'invocation';directory.mkdir()
   command=[sys.executable,'-B','-c','import os,sys; os.write(1,b"a"*100000); os.write(2,b"b"*70000); sys.exit('+str(code)+')']
   (directory/'INPUT.json').write_text(json.dumps({'owned_workspace':str(root),'physical_argv':command}))
   result=subprocess.run([sys.executable,'-B',str(HERE/'code/compile_measure.py'),str(directory)],cwd=root,capture_output=True,env=dict(os.environ,PYTHONPATH=str(HERE/'runtime-tools')))
   self.assertTrue((directory/'PHYSICAL-RESULT.json').exists(),result.stderr.decode(errors='replace')[:2000])
   report=json.loads((directory/'PHYSICAL-RESULT.json').read_text())
   self.assertEqual(result.returncode,code);self.assertEqual(report['returncode'],code)
   self.assertTrue(report['output_capture']['complete']);self.assertEqual(report['output_capture']['errors'],[])
   self.assertEqual(result.stdout,b'a'*100000);self.assertEqual(result.stderr,b'b'*70000)
   for row in report['output_capture']['streams']:
    data=Path(row['path']).read_bytes();self.assertEqual(row['sha256'],hashlib.sha256(data).hexdigest());self.assertEqual(row['bytes'],len(data))
   self.assertEqual((directory/'STDOUT').read_bytes(),result.stdout);self.assertEqual((directory/'STDERR').read_bytes(),result.stderr)
 def test_untruncated_success_streams(self):self.sample(0)
 def test_untruncated_failed_streams_and_exit(self):self.sample(7)
 def test_original_executable_modes_are_preserved(self):
  import json
  layout=json.loads((HERE/'TOOL-LAYOUT.json').read_text())
  original=historical.materialize('/home/cody/zesislar/_build/agents/worker-build-2/private-admission-route-v1/source014/RESTART-TOOLS.json')
  manifest=json.loads(original.read_text())
  for row in manifest['files']:
   relative=manifest['relative_paths'][row['path']]
   current=HERE/layout[relative]
   self.assertEqual(current.stat().st_mode&0o111,Path(row['path']).stat().st_mode&0o111,str(current))
 def test_policy_and_guard_are_unchanged(self):
  original=historical.materialize('/home/cody/zesislar/_build/agents/worker-build-2/private-admission-route-v1/source014/restart-tools/resource_guard.sh')
  # Preserve the reviewed PID identities and the ten-second throttle cache.
  expected=original.read_text()
  needle='      if diagnostic_probe; then\n        local probe_tag=issue10'
  expected=expected.replace(needle,'''      printf 'owner_start=%s\\n' "$(process_start "$owner")" >> "$replacement" || {
        rm -f -- "$replacement"; flock -u 7; exec 7>&-; return 2;
      }
'''+needle)
  expected=expected.replace('        if ! printf \'probe=%s\\nmemory_gib=%s\\ncpu=unlimited\\nowner_start=%s\\n\' \\\n            "$probe_tag" "$MODULE_LIMIT_GIB" "$(process_start "$owner")"','        if ! printf \'probe=%s\\nmemory_gib=%s\\ncpu=unlimited\\n\' \\\n            "$probe_tag" "$MODULE_LIMIT_GIB"')
  expected=expected.replace('  sed -n \'4,$p\' "$marker" >> "$replacement"', '  sed -n \'4,$p\' "$marker" | sed \'/^child_start=/d\' >> "$replacement"')
  needle="  # Marking the child must not restart the confirmation's launch window."
  expected=expected.replace(needle,'''  printf 'child_start=%s\\n' "$(process_start "$child")" >> "$replacement"
'''+needle)
  expected=expected.replace('guards share it for two seconds','guards share it for ten seconds')
  expected=expected.replace('$(date +%s) - stamp >= 2','$(date +%s) - stamp >= 10')
  self.assertEqual((HERE/'runtime-tools/resource_guard.sh').read_text(),expected)
if __name__=='__main__':unittest.main()
