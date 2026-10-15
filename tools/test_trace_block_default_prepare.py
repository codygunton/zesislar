"""Test the default preparation boundary with a refusing mock compiler."""

import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).parent/'block'))
import trace_block_prepare as prepare
import trace_block_package as package


class DefaultPreparationTests(unittest.TestCase):
    def test_default_pipeline_installs_plugin_before_compiling_clients(self):
        route=(prepare.OWNER/'ZesuSsz/Automation/ReturnRoute.v').read_text()
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);original=root/'original';owner=root/'owner'
            files={'ZesuSsz/Automation/All.v':'Require Export ZesuSsz.Automation.Hooks.\n',
                   'ZesuSsz/Automation/Hooks.v':'Ltac zesu_liAStep := idtac.\n',
                   'ZesuSsz/Automation/ReturnRoute.v':route,'dune-project':'(lang dune 3.8)\n(package (name zesu-signature-gates))\n',
                   'ZesuSsz/dune':'(coq.theory (name ZesuSsz) (theories iris stdpp RecordUpdate Ltac2))\n'}
            declaration='Lemma target : True.\n'
            prefix='Require Import ZesuSsz.Automation.All.\nRequire Import ZesuSsz.Automation.ReturnRoute.\n'+declaration+'Proof.\n'
            files['Block.v']=prefix+'Abort.\n'
            for name,text in files.items():
                path=original/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            native=original/'generated/isla-traces/index.v';native.parent.mkdir(parents=True);native.write_text('opaque native bytes')
            for name in package.FILES:
                path=owner/package.FILTERED/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text('package fixture '+name)
            (owner/'META.p0-filtered-trace.template').write_text('directory="."\n# DUNE_GEN\n')
            commands=[]
            def git(workspace,*args):
                if args==('rev-parse','HEAD'):return ('a'*40+'\n').encode()
                if args==('ls-files','-z'):return ('\0'.join(files)+'\0').encode()
                if args==('ls-files','--others','--exclude-standard','-z'):return b''
                if args==('rev-parse','--path-format=absolute','--git-common-dir'):return str(root/'.git').encode()
                raise AssertionError(args)
            def run(command,**kwargs):
                if command[0]=='git':
                    Path(command[-2]).mkdir(parents=True)
                else:
                    build=Path(command[command.index('--build-dir')+1]);workspace=Path(command[command.index('--root')+1])
                    targets=command[command.index('-j32')+1:];commands.append(targets)
                    plugin=build/'install/default/lib/p0-filtered-trace/trace-observer/filtered_trace_plugin.cmxs'
                    if 'p0-filtered-trace.install' in targets:
                        plugin.parent.mkdir(parents=True);plugin.write_bytes(b'plugin fixture')
                        writer=build/'default'/package.WRITER_TARGET;writer.parent.mkdir(parents=True);writer.write_bytes(b'writer fixture')
                    elif 'zesu-signature-gates.install' not in targets:
                        # A client compile fails if preparation races the plugin install.
                        self.assertTrue(plugin.is_file(),'The client started before plugin installation.')
                        for target in targets:
                            path=build/'default'/target;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(b'compiled client fixture')
                        (build/'coqc-ocamlpath.json').write_text(json.dumps({'workspace':str(workspace),'private_build':str(build)}))
                return type('Result',(),{'returncode':0})()
            request={'workspace':str(original),'source':str(original/'Block.v'),'source_prefix':prefix,
                     'declaration':declaration,'prefix_text':'','rule_set':[{'name':'ReturnRoute','enabled':True}],
                     'stop':{'kind':'residual','value':None},'writer_id':'fixture-owner','block_pc':'0x1000',
                     'scope':{'root':'a'*40,'source_sha256':prepare.digest(original/'Block.v')}}
            with patch.object(prepare,'OWNER',owner),patch.object(prepare,'RUNTIME_FILES',()),patch.object(prepare,'_git',side_effect=git),patch.object(prepare.subprocess,'run',side_effect=run),patch.object(prepare.shutil,'which',return_value='/fixture/opam'):
                result=prepare.prepare_request(request,root/'output')
            self.assertEqual(commands[0],['p0-filtered-trace.install',package.WRITER_TARGET])
            self.assertEqual(commands[1],['zesu-signature-gates.install'])
            self.assertIn(package.BRIDGE.replace('.v','.vo'),commands[2])
            self.assertEqual(result['instrumentation']['method'],'source-filtered-v1')
            self.assertIs(result['instrumentation']['entry_coverage_complete'],True)
            self.assertIs(result['instrumentation']['instruction_coverage_complete'],True)
            package.validate_runtime(result)
            source=Path(result['source']).read_text()
            self.assertLess(source.index('Automation.All'),source.index('P0Filtered'))
            self.assertIn('From P0Filtered Require Import TraceObserver.',source)
            self.assertNotIn('Require Import ZesuSsz.Evidence.TraceObserver.',source)
            self.assertEqual((original/'Block.v').read_text(),prefix+'Abort.\n')


if __name__=='__main__':unittest.main()
