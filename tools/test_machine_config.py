import copy
import tomllib
import unittest
from pathlib import Path

from machine_config import DEFAULT_FIELDS, generate_config, read_machine, validate_machine


ROOT = Path(__file__).resolve().parents[1]


class MachineConfigTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / "ZesuSsz/Contracts/Machine.v").read_text()
        self.machine = read_machine(self.source)
        self.template = (ROOT / "ZesuSsz/riscv64_zesu.toml").read_text()

    def test_checked_config_matches_every_sail_field(self):
        generated = generate_config(self.template, self.machine)
        self.assertEqual(generated, self.template)
        settings = tomllib.loads(generated)["registers"]["defaults"]
        for setting, field in DEFAULT_FIELDS.items():
            value = settings[setting]
            if isinstance(value, str):
                value = int(value, 0)
            self.assertEqual(value, self.machine[field])

    def test_source_change_updates_configuration(self):
        machine = copy.deepcopy(self.machine)
        machine["mapClintBase"] += 0x100000
        settings = tomllib.loads(generate_config(self.template, machine))
        self.assertEqual(int(settings["registers"]["defaults"]["rv_clint_base"], 0),
                         machine["mapClintBase"])

    def test_rejects_device_window_inside_ram(self):
        machine = copy.deepcopy(self.machine)
        machine["mapClintBase"] = machine["mapHeapBase"]
        with self.assertRaisesRegex(ValueError, "must not overlap"):
            validate_machine(machine)

    def test_rejects_incomplete_record(self):
        source = self.source.replace("mapRamBase := 0;", "")
        with self.assertRaisesRegex(ValueError, "every field"):
            read_machine(source)


if __name__ == "__main__":
    unittest.main()
