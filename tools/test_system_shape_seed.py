import copy
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
from symbolic_state import Expr, SymbolicState, bits, boolean, evaluate_trace, input_expr
from system_shape_seed import seed_system_shapes


class SystemShapeSeedTests(unittest.TestCase):
    def setUp(self):
        folder = tempfile.TemporaryDirectory()
        self.addCleanup(folder.cleanup)
        self.source = Path(folder.name) / "map.v"
        self.source.write_text("Definition selected_map := source_shapes.\n")
        self.binding = {"path": str(self.source),
                        "sha256": hashlib.sha256(self.source.read_bytes()).hexdigest()}

    def row(self, key="control.bits", **values):
        return {"key": key, "shape": "exact", "sort": "bits", "width": 64,
                "value": bits(3, 64), "source_bindings": [self.binding], **values}

    def seed(self, rows, state=None):
        return seed_system_shapes(state or SymbolicState(), rows,
                                  collection_ownership_id="seed:system")

    def test_exact_values_preserve_original_state_and_collection(self):
        state = SymbolicState(registers={"x1": input_expr("saved")})
        before = state.to_dict()
        result = self.seed([self.row()], state)
        self.assertEqual(state.to_dict(), before)
        self.assertEqual(result.state.registers["control.bits"], bits(3, 64))
        self.assertEqual(result.to_dict()["created_ownership"], [])
        self.assertEqual(result.collection_ownership_id, "seed:system")

    def test_mask_preserves_symbol_and_records_constraint(self):
        symbol = input_expr("source_control")
        result = self.seed([self.row(shape="mask", symbol=symbol,
                                     mask=bits(7, 64), expected=bits(2, 64))])
        self.assertEqual(result.state.registers["control.bits"], symbol)
        self.assertEqual(result.binders[0]["type"], "bv 64")
        self.assertEqual(len(result.state.conditions), 1)
        self.assertEqual(result.state.conditions[0].op, "=")
        self.assertEqual(result.state.conditions[0].args[0].op, "bvand")

    def test_unconstrained_bits_keep_distinct_binders(self):
        result = self.seed([self.row(key, shape="bits", symbol=input_expr(name))
                            for key, name in [("one", "source_one"), ("two", "source_two")]])
        self.assertEqual([r["name"] for r in result.binders], ["source_one", "source_two"])
        self.assertEqual(result.state.conditions, [])

    def test_boolean_and_enum_exact_values(self):
        result = self.seed([self.row("flag", sort="bool", width=None, value=boolean(True)),
                            self.row("mode", sort="enum", width=None, value=Expr("enum", value="Machine"))])
        self.assertEqual(result.state.registers["flag"], boolean(True))
        self.assertEqual(result.state.registers["mode"].value, "Machine")

    def test_changed_or_missing_source_refuses(self):
        with self.assertRaises(ValueError):
            self.seed([self.row(source_bindings=[])])
        self.source.write_text("Definition selected_map := changed.\n")
        with self.assertRaises(ValueError):
            self.seed([self.row()])

    def test_wrong_width_or_unknown_value_refuses(self):
        for value in [bits(3, 32), Expr("unknown_input", width=64, value="capture")]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.seed([self.row(value=value)])

    def test_existing_register_conflict_refuses_without_mutation(self):
        state = SymbolicState(registers={"control.bits": bits(7, 64)})
        before = state.to_dict()
        with self.assertRaises(ValueError):
            self.seed([self.row()], state)
        self.assertEqual(state.to_dict(), before)

    def test_repeated_register_or_symbol_refuses(self):
        with self.assertRaises(ValueError):
            self.seed([self.row(), self.row()])
        with self.assertRaises(ValueError):
            self.seed([self.row(key, shape="bits", symbol=input_expr("same")) for key in ["one", "two"]])

    def test_unrelated_collection_refuses(self):
        with self.assertRaises(ValueError):
            self.seed([self.row(collection_ownership_id="other")])
        with self.assertRaises(ValueError):
            self.seed([self.row(ownership_id="other")])

    def test_symbol_scope_is_preserved(self):
        row = self.row(shape="bits", symbol=input_expr("source_control"),
                       binder={"name": "source_control", "type": "bv 64", "scope": "public_entry"})
        self.assertEqual(self.seed([row]).binders[0]["scope"], "public_entry")
        row["binder"]["name"] = "other"
        with self.assertRaises(ValueError):
            self.seed([row])

    def test_execution_history_cannot_receive_new_initial_values(self):
        state = SymbolicState(trace_count=1)
        with self.assertRaises(ValueError):
            self.seed([self.row()], state)

    def test_serialized_expressions_keep_the_same_result(self):
        row = self.row()
        serialized = copy.deepcopy(row)
        serialized["value"] = row["value"].to_dict()
        self.assertEqual(self.seed([row]).to_dict(), self.seed([serialized]).to_dict())

    def test_source_boolean_controls_trace_feasibility(self):
        trace = '(trace (declare-const f Bool) (read-reg |flag| nil f) (assert f))'
        for enabled, expected in [(True, "complete"), (False, "infeasible")]:
            state = self.seed([self.row("flag", sort="bool", width=None,
                                        value=boolean(enabled))]).state
            with self.subTest(enabled=enabled):
                self.assertEqual(evaluate_trace(trace, state)[0].status, expected)

    def test_enum_read_uses_selected_source_value(self):
        state = self.seed([self.row("mode", sort="enum", width=None,
                                    value=Expr("enum", value="Machine"))]).state
        trace = '(trace (define-enum |Mode| 2 (|Machine| |User|)) (read-reg |mode| nil |Machine|))'
        self.assertEqual(evaluate_trace(trace, state)[0].status, "complete")


if __name__ == "__main__":
    unittest.main()
