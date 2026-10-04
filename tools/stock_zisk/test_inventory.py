"""Focused checks for static inventory measurements."""
import unittest
from inventory import analyze_ranges, cfg_loops, function_body, FUNCTION


class InventoryTests(unittest.TestCase):
    def test_loop_and_exit(self):
        rows=[{'pc':4,'size':4,'mnemonic':'addi','operands':'a0,a0,1'},
              {'pc':8,'size':4,'mnemonic':'bnez','operands':'a0,00000004'},
              {'pc':12,'size':4,'mnemonic':'ret','operands':''}]
        loops=cfg_loops(rows)
        self.assertEqual(len(loops),1)
        self.assertEqual(loops[0]['instruction_count'],2)

    def test_inline_jump_is_not_a_call(self):
        rows=[{'pc':4,'size':4,'mnemonic':'j','operands':'00000020 <label>'}]
        result=analyze_ranges([(4,8)],rows,[4],{})
        self.assertEqual(result['calls'],[])

    def test_external_function_jump_is_a_tail_call(self):
        rows=[{'pc':4,'size':4,'mnemonic':'j','operands':'00000020 <callee>'}]
        result=analyze_ranges([(4,8)],rows,[4],{32:['callee']})
        self.assertEqual(result['calls'][0]['kind'],'tail')

    def test_anonymous_return_struct(self):
        source='pub fn example(a: u64) struct { q: u64 } { return .{ .q = a }; }'
        body=function_body(source,FUNCTION.search(source))
        self.assertIn('return',body)
        self.assertNotIn('q: u64',body)

    def test_stack_frame(self):
        rows=[{'pc':4,'size':4,'mnemonic':'addi','operands':'sp,sp,-16'},
              {'pc':8,'size':4,'mnemonic':'sd','operands':'ra,8(sp)'}]
        result=analyze_ranges([(4,12)],rows,[4,8],{})
        self.assertEqual(result['stack_structure']['sp_adjustments'][0]['bytes'],-16)
        self.assertEqual(result['stack_structure']['direct_sp_offsets'],[8])


if __name__=='__main__':unittest.main()
