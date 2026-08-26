#!/usr/bin/env python3

import json
import unittest
from unittest.mock import patch

import check_parity


class ParityTest(unittest.TestCase):
    def test_reviewed_files_pass(self):
        check_parity.validate()

    def test_changed_source_file_is_rejected(self):
        registry = json.loads(check_parity.REGISTRY.read_text())
        name = next(iter(registry["exactFiles"]))
        real = check_parity.sha256

        def forged(path):
            return "0" * 64 if path.name == name else real(path)

        with patch.object(check_parity, "sha256", forged):
            with self.assertRaisesRegex(ValueError, name):
                check_parity.validate()


if __name__ == "__main__":
    unittest.main()
