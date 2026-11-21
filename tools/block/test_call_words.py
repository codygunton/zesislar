import unittest

from call_boundary import passed_arguments, record_word_term


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


class PassedArgumentsTest(unittest.TestCase):
    FACTS = ['nextUint64CallDomain (args call20_arg_word_1_0 (take (bv_unsigned call20_arg_word_1_8) b))',
             'call20_word_1_0 = Z_to_bv 64 (nextRestPointer (call20_result))']

    def test_record_defined_word_is_its_term_and_no_binder(self):
        components = [{'id': 'call19_facts', 'kind': 'opaque', 'source': RECORD}]
        passed = {'call20_arg_word_1_0': 'call19_word_1_0', 'call20_arg_word_1_8': 'call19_word_1_8'}
        facts, named = passed_arguments(self.FACTS, passed, components)
        self.assertEqual(named, {})
        self.assertEqual(facts[0], 'nextUint64CallDomain (args (Z_to_bv 64 (nextRestPointer (call19_result))) '
                                   '(take (bv_unsigned (Z_to_bv 64 (nextRestLength (call19_result)))) b))')
        self.assertEqual(facts[1], self.FACTS[1])

    def test_undefined_word_stays_a_named_binder(self):
        components = [{'id': 'r', 'kind': 'register', 'source': '"x10" ↦ᵣ RVal_Bits call19_word_1_0'}]
        passed = {'call20_arg_word_1_0': 'call19_word_1_0'}
        facts, named = passed_arguments(self.FACTS, passed, components)
        self.assertEqual(named, passed)
        self.assertEqual(facts, self.FACTS)


if __name__ == '__main__':
    unittest.main()
