"""Compare emitted unsigned constraints with mathematical access intervals."""
from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_access_regions as baseline
from access_regions import access_constraint, region_bounds


def evaluate(text, variables):
    tokens = iter(re.findall(r"\(|\)|[^\s()]+", text))
    def read(token):
        if token == "(":
            operator = next(tokens)
            values = []
            for item in tokens:
                if item == ")":
                    break
                values.append(read(item))
            if operator == "and": return all(values)
            if operator == "or": return any(values)
            if operator == "bvule": return values[0] <= values[1]
            if operator == "bvult": return values[0] < values[1]
            if operator == "bvadd": return (values[0] + values[1]) % (1 << 64)
            if operator == "bvsub": return (values[0] - values[1]) % (1 << 64)
            raise AssertionError("Unexpected SMT operator: " + operator)
        if token == "false": return False
        if token == "true": return True
        if token.startswith("#x"):
            assert len(token) == 18, token
            return int(token[2:], 16)
        return variables[token]
    value = read(next(tokens))
    assert next(tokens, None) is None
    return value


class UnsignedAccessTests(unittest.TestCase):
    def test_emitted_regions_equal_full_integer_intervals(self):
        word = 1 << 64
        factory = baseline.AccessRegionTests()
        with tempfile.TemporaryDirectory() as directory:
            for immediate in [-8, 0, 24]:
                packet, access, instruction = factory.fixture(
                    Path(directory), immediate=immediate,
                    regions=["INPUT_BUFFER", "RODATA", "RAM"])
                bounds = region_bounds(packet)
                text, record = access_constraint(packet, access, instruction, bounds)
                self.assertEqual(record["comparison_width"], 64)
                self.assertEqual(record["source_comparison_width"], 128)
                self.assertNotRegex(text, r"\(bvs(?:lt|le|gt|ge)\b")
                width = instruction["width"]
                addresses = {0, 1, word - width, word - 1}
                for lower, upper in bounds.values():
                    addresses.update([lower - 1, lower, lower + 1,
                                      upper - width, upper - width + 1, upper])
                ends = [0, width - 1, width, word - 1]
                lower, upper = bounds["INPUT_BUFFER"]
                ends.extend([lower + width - 1, lower + width, upper])
                for address in addresses:
                    for input_end in ends:
                        expected = any(lower <= address and address + width <= upper
                            and (name != "INPUT_BUFFER" or address + width <= input_end)
                            for name, (lower, upper) in bounds.items())
                        actual = evaluate(text, {"x2": (address - immediate) % word,
                                                 "zisk_input_end": input_end})
                        self.assertEqual(actual, expected, (address, input_end, immediate))

    def test_region_at_word_end_has_no_wrapping_endpoint(self):
        word = 1 << 64
        factory = baseline.AccessRegionTests()
        with tempfile.TemporaryDirectory() as directory:
            packet, access, instruction = factory.fixture(Path(directory))
            packet["regions"]["RAM"] = {"lower": word - 16, "upper": word}
            text, _ = factory.render(packet, access, instruction)
            for address, expected in [(word - 17, False), (word - 16, True),
                                      (word - 8, True), (word - 7, False), (0, False)]:
                self.assertEqual(evaluate(text, {"x2": address}), expected)

    def test_region_smaller_than_access_is_false(self):
        factory = baseline.AccessRegionTests()
        with tempfile.TemporaryDirectory() as directory:
            packet, access, instruction = factory.fixture(Path(directory))
            packet["regions"]["RAM"] = {"lower": 0, "upper": 1}
            text, _ = factory.render(packet, access, instruction)
            self.assertEqual(text, "false")


if __name__ == "__main__":
    unittest.main()
