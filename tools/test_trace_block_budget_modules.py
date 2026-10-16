"""Import the writer and validator together under their publication names."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
import trace_block_raw_budget as writer
import trace_block_raw_budget_validation as validation


class BudgetModuleTests(unittest.TestCase):
    def test_writer_and_validation_import_together(self):
        self.assertIsNot(writer, validation)
        self.assertEqual(Path(writer.__file__).name, 'trace_block_raw_budget.py')
        self.assertEqual(Path(validation.__file__).name, 'trace_block_raw_budget_validation.py')
        self.assertTrue(callable(writer.RawBudget))
        self.assertTrue(callable(validation.verify_raw_budget))
        self.assertTrue(callable(validation.validate_ledger))
        self.assertEqual(validation.RAW_LIMIT_BYTES, 2_000_000_000)


if __name__ == '__main__':
    unittest.main()
