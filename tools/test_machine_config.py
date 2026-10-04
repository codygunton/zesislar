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
        machine["mapInsnsPerTick"] += 1
        settings = tomllib.loads(generate_config(self.template, machine))
        self.assertEqual(settings["registers"]["defaults"]["rv_insns_per_tick"],
                         machine["mapInsnsPerTick"])

    def test_rejects_device_window_inside_ram(self):
        machine = copy.deepcopy(self.machine)
        machine["mapClintBase"] = machine["mapHeapBase"]
        machine["mapClintSize"] = 0x100
        with self.assertRaisesRegex(ValueError, "must not overlap"):
            validate_machine(machine)

    def test_accepts_separate_read_only_input(self):
        self.assertLessEqual(self.machine["mapInputBufferAddress"] +
                             self.machine["mapInputCapacity"], self.machine["mapRamBase"])
        self.assertIsNone(self.machine["mapIoContextAddress"])
        self.assertIsNone(self.machine["mapZkvmExitPc"])
        validate_machine(self.machine)

    def test_populated_section_permissions(self):
        sections = self.machine['mapPopulatedSections']
        self.assertEqual(len(sections), 4)
        self.assertEqual([(s['sectionReadable'], s['sectionWritable'], s['sectionExecutable'])
                          for s in sections],
                         [(False, False, True), (True, False, False),
                          (True, True, False), (True, True, False)])
        self.assertEqual(sections[2]['sectionFileEnd'], sections[2]['sectionBase'])
        self.assertEqual(sections[2]['sectionEnd'], sections[3]['sectionBase'])

    def test_rejects_invalid_populated_extent(self):
        source = self.source.replace('sectionFileEnd := 0x8010fd78',
                                     'sectionFileEnd := 0xffffffffffffffff')
        with self.assertRaisesRegex(ValueError, 'populated section extent'):
            read_machine(source)

    def test_rejects_input_overlapping_writable_ram(self):
        machine = copy.deepcopy(self.machine)
        machine["mapInputBufferAddress"] = machine["mapRamBase"]
        with self.assertRaisesRegex(ValueError, "must not overlap"):
            validate_machine(machine)

    def test_rejects_fork_instance(self):
        with self.assertRaisesRegex(ValueError, "historical forkMap"):
            read_machine(self.source, "forkMap")

    def test_rejects_fixed_adapter_input_register(self):
        for register in ["zisk_input_end", "zisk_free_input"]:
            for section in ["defaults", "reset"]:
                template = self.template.replace(f"[registers.{section}]",
                    f'[registers.{section}]\n{register} = "0x40000008"')
                with self.subTest(register=register, section=section):
                    with self.assertRaisesRegex(ValueError, "remain dynamic"):
                        generate_config(template, self.machine)

    def test_rejects_fixed_adapter_input_constraint(self):
        template = self.template.replace('[constraints]',
            '[constraints]\ninput = ["= zisk_input_end 0x40000008"]')
        with self.assertRaisesRegex(ValueError, "remain dynamic"):
            generate_config(template, self.machine)

    def test_rejects_incomplete_record(self):
        source = self.source.replace(f"mapRamBase := {hex(self.machine['mapRamBase'])};", "")
        with self.assertRaisesRegex(ValueError, "every field"):
            read_machine(source)


if __name__ == "__main__":
    unittest.main()
