"""Adapt preserved argument tests to the explicit shared CLI."""
from pathlib import Path
import hashlib,json,tempfile,atexit
import scratch
import _historical_fixtures as historical
LEGACY=historical.directory('/home/cody/zesislar/.worktrees/infra-a-check-entry-chain-3e40')
BASE=LEGACY/'_build/check-entry-stage1-passfix-ten-runtime-v2'
SOURCE=LEGACY/'_build/check-entry-passfix045-ten-source-v1'
TMP=Path('/home/cody/.cache/zesislar/shared-harness-tests')
TMP.mkdir(parents=True,exist_ok=True)
_temporary=tempfile.TemporaryDirectory(dir=TMP)
atexit.register(_temporary.cleanup)
root=Path(_temporary.name)
def binding(path):return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
adapter=root/'ADAPTER.json'
adapter.write_text(json.dumps({'targets':binding(SOURCE/'NATIVE-TARGETS.json')}))
def arguments(argv):
 argv=list(argv)
 explicit_base='--base-runtime' in argv
 defaults={'--harness-commit':'0'*40,'--target-adapter':str(adapter),'--base-runtime':str(BASE/'release-v1/RUNTIME.json'),'--base-runtime-sha256':binding(BASE/'release-v1/RUNTIME.json')['sha256']}
 for key,value in defaults.items():
  if key=='--base-runtime-sha256' and explicit_base:continue
  if key not in argv:argv += [key,value]
 return scratch.arguments(argv)
