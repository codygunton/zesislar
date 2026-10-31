import subprocess,unittest
from pathlib import Path
HERE=Path(__file__).resolve().parent
class Guard24(unittest.TestCase):
 def reason(self,count,key='new'):
  text=(HERE/'runtime-tools/resource_guard.sh').read_text();start=text.index('probe_admission_reason() {');end=text.index('\n}',start)+2;function=text[start:end]
  script="probe_keys() { for ((i=0;i<"+str(count)+";i++)); do printf 'aggregate:a%s\\n' \"$i\"; done; }; probe_owner_aggregate() { echo \"$2\"; }; process_start() { echo 1; }; "+function+"; ZESU_AGGREGATE_SLICE="+key+"; probe_admission_reason 123"
  result=subprocess.run(['/bin/bash','-c',script],capture_output=True,text=True,check=True);return result.stdout.strip()
 def test_23_aggregates_allow_new(self):self.assertEqual(self.reason(23),'')
 def test_24_aggregates_refuse_new(self):self.assertIn('twenty-four-aggregate',self.reason(24))
 def test_24_aggregates_allow_existing_nested_request(self):self.assertEqual(self.reason(24,'a0'),'')
 def test_25_aggregates_refuse_new(self):self.assertIn('twenty-four-aggregate',self.reason(25))
if __name__=='__main__':unittest.main()
