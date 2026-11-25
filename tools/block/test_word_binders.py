"""Profile `word_binders`: a listed slot of a stored byte array is stated through a fresh binder and the
visible named equation of the term it held; without a row the entry renders as before."""
from pathlib import Path
import json
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / 'oblig'))
import annotations  # noqa: E402
import entry_hist  # noqa: E402
from function_profiles import resolve_symbol_keys  # noqa: E402
from render_support import component_source  # noqa: E402

SP = 'bv_unsigned (txStackPointer args)'
WORD = 'bv_or (f x) (g y)'
# A 16-byte stored array at sp - 32: one word W at bytes 0..7, eight literal bytes after it.
ITEMS = ['(bv_extract %d%%N 8%%N (%s))' % (8 * index, WORD) for index in range(8)] + \
        ['(BV 8%%N %d%%Z)' % index for index in range(8)]
ARRAY = {'kind': 'byte_array', 'address': '((%s - 32))%%Z' % SP, 'value': '[' + '; '.join(ITEMS) + ']'}
REGISTER = {'kind': 'register', 'name': 'x10', 'value': 'RVal_Bits (x)'}
PLAIN = [{'name': 'args', 'type': 'A'}, {'name': 'returnAddress', 'type': 'Z'}]


def slot(name, offset=0, size=8, region=SP + ' - 32'):
    return {'region': region, 'offset': offset, 'size': size, 'name': name}


def render(components):
    return [component_source(component, {}, {'source_hashes': {}}, HERE.parents[1], None)
            for component in components]


class Symbols(dict):
    """Every symbol resolves: the function at 0x80000000, any callee at 0x80100000."""
    def __contains__(self, name):
        return True

    def __missing__(self, name):
        return 0x80100000


def profile_fixture(rows=()):
    """A small annotation file (nextUint64's) with the given word_binders rows, compiled and resolved."""
    data = json.loads((HERE.parent / 'oblig/testdata/nextUint64.annotations.json').read_text())
    data['rows'].extend(rows)
    compiled = annotations.compile_profile(data)
    return resolve_symbol_keys(compiled, Symbols({compiled['symbol']: 0x80000000}))


class Profile(unittest.TestCase):
    def test_a_row_compiles_to_the_slots_of_each_site(self):
        row = {'id': 'words', 'at': {'pc': '+0x10', 'boundary': 'word_binders'}, 'slots': [slot('w')]}
        self.assertEqual(profile_fixture([row])['word_binders'], {'0010': [slot('w')]})
        sites = dict(row, sites=['+0x10', '+0x20'])
        self.assertEqual(sorted(profile_fixture([sites])['word_binders']), ['0010', '0020'])
        self.assertNotIn('word_binders', profile_fixture())

    def test_malformed_rows_are_refused(self):
        base = {'id': 'words', 'at': {'pc': '+0x10', 'boundary': 'word_binders'}}
        for row in ({**base, 'slots': []}, {**base, 'slots': [{**slot('w'), 'offset': '8'}]},
                    {**base, 'slots': [slot('w'), slot('w', 8)]}, {**base, 'slots': [slot('w')], 'sites': ['sym+0x10']},
                    {**base, 'slots': [{**slot('w'), 'extra': 1}]}):
            with self.subTest(row=row), self.assertRaises(annotations.AnnotationError):
                profile_fixture([row])


class EntryComponents(unittest.TestCase):
    def test_a_word_slot_renders_as_binder_and_named_equation(self):
        profile = profile_fixture([{'id': 'words', 'at': {'pc': '+0x10', 'boundary': 'word_binders'},
                                    'slots': [slot('w')]}])
        components, binders, facts, reports = entry_hist.word_binder_components(
            [REGISTER, ARRAY], profile['word_binders']['0010'], {'x'})
        texts = render(components)
        self.assertEqual(texts[0], render([REGISTER])[0])
        self.assertEqual(texts[1], '(((%s - 32))%%Z) ↦ₘ∗ ([' % SP
                         + '; '.join(['bv_extract %d%%N 8%%N w' % (8 * index) for index in range(8)] + ITEMS[8:]) + '])')
        self.assertEqual(binders, [{'name': 'w', 'type': 'bv 64'}])
        self.assertEqual(facts, ['zesu_named_eq w (%s)' % WORD])
        self.assertEqual(reports[0]['applied'], ['w'])
        # The frame-cell reading of the slot is the binder itself.
        self.assertEqual(entry_hist._word_of_bytes(entry_hist._list_items(components[1]['value'])[:8]), 'w')

    def test_without_a_row_the_components_render_as_before(self):
        components, binders, facts, reports = entry_hist.word_binder_components([REGISTER, ARRAY], [], {'x'})
        self.assertEqual(render(components), render([REGISTER, ARRAY]))
        self.assertEqual((binders, facts, reports), ([], [], []))
        # A row of another region leaves the array as it is.
        other = entry_hist.word_binder_components([ARRAY], [slot('w', region=SP + ' - 64')], set())
        self.assertEqual(other, ([ARRAY], [], [], []))

    def test_a_byte_list_slot_is_the_whole_array(self):
        address = '(((%s - 64) + 40))%%Z' % SP   # the same slot, spelled as the entry renders it
        array = dict(ARRAY, address=address)
        components, binders, facts, _ = entry_hist.word_binder_components(
            [array], [slot('l', offset=8, size=16, region=SP + ' - 32')], set())
        self.assertEqual(render(components), ['((((%s - 64) + 40))%%Z) ↦ₘ∗ (l)' % SP])
        self.assertEqual(binders, [{'name': 'l', 'type': 'list byte'}])
        self.assertEqual(facts, ['zesu_named_eq l (%s)' % ARRAY['value']])

    def test_refused_slots_keep_their_bytes(self):
        cases = [(slot('w', offset=8), 'not bv_extract'),          # literal bytes, not one word
                 (slot('l', size=12), 'whole 16-byte array'),       # a byte list inside the array
                 (slot('w', offset=12), 'crosses the end'),
                 (slot('x'), 'already an entry binder')]
        for row, reason in cases:
            with self.subTest(row=row):
                change = entry_hist.word_binder_value(ARRAY['address'], ARRAY['value'], [row], {'x'})
                self.assertEqual(change['value'], ARRAY['value'])
                self.assertEqual((change['binders'], change['facts'], change['applied']), ([], [], []))
                self.assertIn(reason, change['refused'][0][1])
        change = entry_hist.word_binder_value(ARRAY['address'], ARRAY['value'],
                                              [slot('w'), slot('v', offset=4)], set())
        self.assertEqual([row['name'] for row in change['applied']], ['w'])
        self.assertIn('overlaps', change['refused'][0][1])

    def test_address_offsets(self):
        self.assertEqual(entry_hist.address_offset('((((%s - 424) + 40) + 40))%%Z' % SP), (SP, -344))
        self.assertEqual(entry_hist.address_offset('bv_unsigned (f (a - 3))'), ('bv_unsigned (f (a - 3))', 0))


class Visibility(unittest.TestCase):
    def setUp(self):
        entry_hist.configure({'entry_hist': 'wrap'})

    def test_the_named_equation_stays_visible_and_keeps_its_binders_live(self):
        binders = [{'name': 'w', 'type': 'bv 64'}, {'name': 'g', 'type': 'bv 64'}]
        resources = ['(a) ↦ₘ∗ ([bv_extract 0%N 8%N w])']
        facts = ['(zesu_named_eq w (h g))', '(P g)']
        _, body, meta = entry_hist.seal_alternative('e', ' (args : A) (returnAddress : Z)', PLAIN, binders,
                                                    resources, facts, [entry_hist.word_binder_pattern('w')])
        self.assertEqual(meta['visible'], ['(zesu_named_eq w (h g))'])
        self.assertEqual([binder['name'] for binder in meta['live']], ['w', 'g'])
        self.assertIn('⌜(zesu_named_eq w (h g))⌝', body)
        # Without the pattern the equation would sit in the history with g a ghost.
        _, _, hidden = entry_hist.seal_alternative('e', ' (args : A) (returnAddress : Z)', PLAIN, binders,
                                                   resources, facts)
        self.assertIn('(zesu_named_eq w (h g))', hidden['hidden'])

    def test_a_loop_class_states_the_slot_through_its_binder(self):
        resources = ['"x10" ↦ᵣ RVal_Bits (x : bv 64%N)', '(%s) ↦ₘ∗ (%s)' % (ARRAY['address'], ARRAY['value'])]
        arguments = ('c', 'Definition c (args : A) (returnAddress : Z) ', '(x : bv 64)', resources,
                     ['bv_unsigned x < 8'], PLAIN, {})
        self.assertIsNone(entry_hist.seal_class(*arguments, visible=['.*']))
        _, text, meta = entry_hist.seal_class(*arguments, visible=['.*'], word_binders=[slot('w')])
        self.assertIn('(w : bv 64)', text)
        self.assertIn('bv_extract 0%N 8%N w;', text)
        self.assertIn('(zesu_named_eq w (%s))' % WORD, text)
        self.assertEqual(meta['word_binders'], {'applied': ['w'], 'refused': []})


if __name__ == '__main__':
    unittest.main()
