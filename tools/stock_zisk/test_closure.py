import unittest

from closure import analyze, switch_targets
from riscv import decode, decode_range, simple_transfers


def words(*values):
    return b''.join(value.to_bytes(4,'little') for value in values)


class ImageFixture:
    def __init__(self, code, slots=None):
        self.code = code
        self.slots = slots or [0x5000,0x6000,0x7000,0x8000]
        self.symbols = {'alt_fl_alloc.vtable':{'st_value':0x4000}}

    def rows(self, name):
        return simple_transfers(decode_range(0x1000,self.code))

    def read(self, address, size):
        if address < 0x4000 or address+size > 0x4020: raise ValueError(address)
        data = b''.join(value.to_bytes(8,'little') for value in self.slots)
        return data[address-0x4000:address-0x4000+size]


class DecodeTests(unittest.TestCase):
    def test_pc_relative_call(self):
        rows = simple_transfers(decode_range(0x1000,words(0x00001097,0xffc080e7)))
        self.assertEqual((rows[1]['kind'],rows[1]['target']),('call',0x1ffc))

    def test_negative_branch(self):
        row = decode(0x1010,words(0xfe059ce3))
        self.assertEqual((row['kind'],row['target']),('branch',0x1008))

    def test_unsupported_extensions(self):
        for word, extension in [(0x00000001,'RVC'),(0x1000202f,'A'),(0x00000053,'FP'),
                                (0x00000073,'ecall'),(0x60001013,'Zb-or-other-extension')]:
            with self.subTest(extension=extension):
                row = decode(0x1000,words(word))
                self.assertEqual((row['kind'],row['extension']),('unsupported',extension))

    def test_memcpy_csr_is_explicit(self):
        row = decode(0x1000,words(0x8135a073))
        self.assertEqual((row['kind'],row['csr']),('runtime',0x813))

    def test_unknown_register_target_stays_unresolved(self):
        image = ImageFixture(words(0x00053703,0x000700e7,0x00008067))
        result = analyze(image,'unconstrained')
        self.assertEqual([r['pc'] for r in result['unresolved']],[0x1004])

    def test_selected_vtable_slot(self):
        # ld t0,8(a1); ld a6,16(t0); jalr a6; ret.
        image = ImageFixture(words(0x0085b283,0x0102b803,0x000800e7,0x00008067))
        result = analyze(image,'rlp_decode.txAccessList')
        self.assertEqual(result['unresolved'],[])
        self.assertEqual(result['calls'][0]['target'],0x7000)
        image.slots[2] = 0x9870
        self.assertEqual(analyze(image,'rlp_decode.txAccessList')['calls'][0]['target'],0x9870)

    def test_switch_checks_target_boundaries(self):
        code = words(0x0ff67513,0x00003597,0x00351513,0xffc58593,
                     0x00a58533,0x00053503,0x00050067,0x00008067)
        rows = simple_transfers(decode_range(0x1000,code))
        class Table:
            def read(self,address,size):
                self.address,self.size = address,size
                return b''.join((0x101c).to_bytes(8,'little') for _ in range(5))
        table = Table()
        result = switch_targets(table,rows)
        self.assertEqual((table.address,table.size),(0x4000,40))
        self.assertEqual(result['index_bounds'],[0,4])
        table.read = lambda address,size: (0x101d).to_bytes(8,'little')*5
        with self.assertRaisesRegex(ValueError,'boundary'): switch_targets(table,rows)


if __name__ == '__main__': unittest.main()
