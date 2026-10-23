"""Check dependency paths when the Dune build directory is a symlink."""

from importlib.machinery import SourceFileLoader
from importlib.util import module_from_spec, spec_from_loader
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


SHIM = Path(__file__).with_name("canonical-bin") / "coqdep"
spec = spec_from_loader("coqdep_canonical", SourceFileLoader("coqdep_canonical", str(SHIM)))
coqdep = module_from_spec(spec)
spec.loader.exec_module(coqdep)


class CanonicalDependencyTests(unittest.TestCase):
    def test_resolves_findlib_paths_without_changing_other_variables(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            physical = root / "_build/agents/private/install/lib"
            physical.mkdir(parents=True)
            alias = root / "_dune-cache"
            alias.symlink_to(physical.parent.parent)
            environment = {"OCAMLPATH": str(alias / "install/lib") + os.pathsep,
                           "UNCHANGED": "literal value"}
            result = coqdep.compiler_environment(environment)
            self.assertEqual(result["OCAMLPATH"], str(physical) + os.pathsep)
            self.assertEqual(result["UNCHANGED"], "literal value")
            self.assertIn("_dune-cache", environment["OCAMLPATH"])
            self.assertEqual(coqdep.compiler_environment({"PATH": "same"}), {"PATH": "same"})

    def test_executes_original_dependency_tool_once_with_exact_arguments(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = root / "coqdep"
            original.write_text("#!/usr/bin/env python3\nimport json,os,sys\n"
                                "print(json.dumps([sys.argv[1:],os.environ['OCAMLPATH']]))\n")
            original.chmod(0o755)
            physical = root / "physical"
            physical.mkdir()
            alias = root / "alias"
            alias.symlink_to(physical)
            environment = dict(os.environ, PATH=str(SHIM.parent) + os.pathsep + str(root)
                               + os.pathsep + os.environ["PATH"], OCAMLPATH=str(alias))
            result = subprocess.run([str(SHIM), "-Q", "path with spaces", "Logical"],
                                    env=environment, text=True, capture_output=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout),
                             [["-Q", "path with spaces", "Logical"], str(physical)])


if __name__ == "__main__":
    unittest.main()
