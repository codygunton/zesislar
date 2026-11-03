import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from source_register_origins import translate_unused_declaration

RAW = '''(trace
 (declare-const v4 (_ BitVec 64))
 (assume (= (bvand (|status| ((_ field |bits|))) #x0000000000020000) #x0000000000000000))
 (assert (= (bvand v4 #x0000000000020000) #x0000000000000000))
 (cycle))'''
ROCQ = '''From isla Require Import opsem.
Definition a1000 : isla_trace :=
 Smt (DeclareConst 4%Z (Ty_BitVec 64%N)) Mk_annot :t:
 Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Val (AVal_Var "status" [Field "bits"]) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x20000%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
 tnil.
'''


class SourceRegisterOriginsTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def inputs(self, raw=RAW, rocq=ROCQ):
        def write(name, text):
            path = self.root / name
            path.write_text(text)
            return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
        raw_binding, rocq_binding = write('trace.isla', raw), write('trace.v', rocq)
        identity = {'kind': 'trace_local', 'pc': '0x1000',
                    'trace_sha256': raw_binding['sha256'], 'declaration': 'v4',
                    'rocq_trace_sha256': rocq_binding['sha256']}
        key = hashlib.sha256(json.dumps(identity, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        return [raw_binding, rocq_binding], dict(pc=0x1000, declaration='v4', width=64, source_key=key)

    def test_actual_register_origin_preserves_key_and_artifacts(self):
        args, options = self.inputs()
        before = [Path(row['path']).read_bytes() for row in args]
        result = translate_unused_declaration(*args, **options)
        self.assertEqual((result['register'], result['field']), ('status', 'bits'))
        self.assertEqual(result['source_key'], options['source_key'])
        self.assertFalse(result['values_selected'])
        self.assertFalse(result['proof_scripts_emitted'])
        self.assertEqual(before, [Path(row['path']).read_bytes() for row in args])

    def test_used_declaration_refuses(self):
        args, options = self.inputs(rocq=ROCQ.replace(' tnil.', ' ReadReg "x1" [] (RegVal_Base (Val_Symbolic 4%Z)) Mk_annot :t: tnil.'))
        with self.assertRaisesRegex(ValueError, 'used by'):
            translate_unused_declaration(*args, **options)

    def test_changed_consumed_field_refuses(self):
        args, options = self.inputs(rocq=ROCQ.replace('Field "bits"', 'Field "other"'))
        with self.assertRaisesRegex(ValueError, 'guard differs'):
            translate_unused_declaration(*args, **options)

    def test_missing_assertion_refuses(self):
        args, options = self.inputs(raw=RAW.replace('(assert', '(unsupported'))
        with self.assertRaisesRegex(ValueError, 'guard pair'):
            translate_unused_declaration(*args, **options)

    def test_unrelated_assertion_refuses(self):
        args, options = self.inputs(raw=RAW.replace('(bvand v4', '(bvand v5'))
        with self.assertRaisesRegex(ValueError, 'does not identify'):
            translate_unused_declaration(*args, **options)

    def test_wrong_width_refuses(self):
        args, options = self.inputs()
        options['width'] = 32
        with self.assertRaisesRegex(ValueError, 'declaration is missing'):
            translate_unused_declaration(*args, **options)

    def test_symbolic_width_refuses(self):
        args, options = self.inputs()
        options['width'] = 'width'
        with self.assertRaisesRegex(ValueError, 'closed positive'):
            translate_unused_declaration(*args, **options)

    def test_changed_key_refuses(self):
        args, options = self.inputs()
        options['source_key'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'source key'):
            translate_unused_declaration(*args, **options)

    def test_changed_artifact_refuses(self):
        args, options = self.inputs()
        Path(args[1]['path']).write_text(ROCQ + '(* changed *)')
        with self.assertRaisesRegex(ValueError, 'artifact changed'):
            translate_unused_declaration(*args, **options)

    def test_ambiguous_projection_refuses(self):
        raw = RAW.replace('#x0000000000020000', '(|other| ((_ field |bits|)))')
        args, options = self.inputs(raw=raw)
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            translate_unused_declaration(*args, **options)

    def test_wrong_instruction_refuses(self):
        args, options = self.inputs(rocq=ROCQ.replace('Definition a1000', 'Definition a1004'))
        with self.assertRaisesRegex(ValueError, 'instruction definition'):
            translate_unused_declaration(*args, **options)

    def test_unsupported_guard_refuses(self):
        args, options = self.inputs(raw=RAW.replace('bvand', 'bvadd'))
        with self.assertRaisesRegex(ValueError, 'guard is unsupported'):
            translate_unused_declaration(*args, **options)


if __name__ == '__main__':
    unittest.main()
