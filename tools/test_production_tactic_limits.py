import re
import unittest
from pathlib import Path


def without_comments(source):
    result = []
    depth = 0
    index = 0
    while index < len(source):
        if source.startswith('(*', index):
            depth += 1
            index += 2
        elif depth and source.startswith('*)', index):
            depth -= 1
            index += 2
        else:
            if not depth:
                result.append(source[index])
            index += 1
    if depth:
        raise ValueError('The comment is not closed')
    return ''.join(result)


class ProductionTacticLimits(unittest.TestCase):
    def test_active_tactics_have_no_deadline(self):
        root = Path(__file__).resolve().parents[1]
        paths = list((root / 'ZesuSsz/Automation').rglob('*.v'))
        paths += list((root / 'InstrSpecs').rglob('*.v'))
        for path in paths:
            with self.subTest(path=path.relative_to(root)):
                self.assertIsNone(re.search(r'\b(?:timeout|Timeout)\b',
                                            without_comments(path.read_text())))

    def test_nested_comments_do_not_mask_a_deadline(self):
        source = '(* timeout (* timeout *) timeout *) timeout 2 idtac.'
        self.assertEqual(without_comments(source).strip(), 'timeout 2 idtac.')


if __name__ == '__main__':
    unittest.main()
