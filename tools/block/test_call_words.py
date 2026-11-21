import unittest

from call_boundary import record_word_term


RECORD = ('⌜∃ (call19_arg_x12 : bv 64), (nextUint64CallMeaning (args [call19_arg_x12]) (call19_result)) '
          '/\\ (call19_word_1_0 = Z_to_bv 64 (nextRestPointer (call19_result))) '
          '/\\ (call19_word_1_8 = Z_to_bv 64 (nextRestLength (call19_result)))⌝')


class RecordWordTermTest(unittest.TestCase):
    def test_passed_word_is_its_record_field(self):
        components = [{'id': 'call19_facts', 'kind': 'opaque', 'source': RECORD}]
        self.assertEqual(record_word_term('call19_word_1_0', components),
                         '(Z_to_bv 64 (nextRestPointer (call19_result)))')
        self.assertEqual(record_word_term('call19_word_1_8', components),
                         '(Z_to_bv 64 (nextRestLength (call19_result)))')

    def test_no_record_keeps_the_word(self):
        components = [{'id': 'r', 'kind': 'register', 'source': '"x10" ↦ᵣ RVal_Bits call19_word_1_0'},
                      {'id': 'g', 'kind': 'opaque', 'source': '⌜bool_decide (call19_word_1_0 = 0) = true⌝'}]
        self.assertIsNone(record_word_term('call19_word_1_0', components))

    def test_term_on_a_bound_name_or_two_terms_is_refused(self):
        bound = [{'id': 'f', 'kind': 'opaque', 'source': '⌜∃ (r : NextUint64Return), (w = Z_to_bv 64 (nextRestPointer r))⌝'}]
        self.assertIsNone(record_word_term('w', bound))
        two = [{'id': 'a', 'kind': 'opaque', 'source': '⌜(w = x)⌝'},
               {'id': 'b', 'kind': 'opaque', 'source': '⌜(w = y)⌝'}]
        self.assertIsNone(record_word_term('w', two))
        same = [{'id': 'a', 'kind': 'opaque', 'source': '⌜(w = x)⌝'},
                {'id': 'b', 'kind': 'opaque', 'source': '⌜(w = x) /\\ True⌝'}]
        self.assertEqual(record_word_term('w', same), '(x)')


if __name__ == '__main__':
    unittest.main()
