import contextlib
import io
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import check_spec_shapes

from check_spec_shapes import (
    binder_shape,
    definitions,
    existential_binders,
    failures,
    resource_parts,
    shape_counts,
    typeclasses_opaque,
    unfold_opacity_count,
    unfold_targets,
)


class SpecShapeTests(unittest.TestCase):
    def test_inventory_rejects_a_newly_staged_module(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.com",
                            "commit", "-q", "--allow-empty", "-m", "Base"],
                           cwd=root, check=True)
            base = subprocess.check_output(["git", "rev-parse", "HEAD"],
                                           cwd=root, text=True).strip()
            name = "ZesuSsz/Evidence/Staged.v"
            source = root / name
            source.parent.mkdir(parents=True)
            source.write_text("Lemma staged : True. Proof. exact I. Qed.")
            subprocess.run(["git", "add", name], cwd=root, check=True)
            with patch.object(check_spec_shapes, "ROOT", root):
                errors = check_spec_shapes.scoped_inventory_errors(
                    {"base_commit": base, "modules": {}}, {name: source.read_text()})
                self.assertEqual(errors, ["Missing shape inventory: " + name])
                self.assertEqual(check_spec_shapes.scoped_inventory_errors(
                    {"base_commit": base, "modules": {name: {}}},
                    {name: source.read_text()}), [])

    def test_main_checks_added_replacement_and_skips_deleted_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            replacement = 'ZesuSsz/Proofs/DecodeItem/Auto/Join6ae0From6a38.v'
            retired = 'ZesuSsz/Proofs/DecodeItem/Join6ae0/From6a38.v'
            (root / replacement).parent.mkdir(parents=True)
            (root / replacement).write_text('Lemma covered : True. Proof. exact I. Qed.')
            baseline = root / 'baseline.json'
            baseline.write_text('{}')
            inventory_file = root / 'inventory.json'
            inventory_file.write_text(json.dumps({'base_commit': 'base', 'modules': {}}))
            with patch.object(check_spec_shapes, 'ROOT', root), \
                 patch.object(check_spec_shapes, 'BASELINE', baseline), \
                 patch.object(check_spec_shapes, 'INVENTORY', inventory_file), \
                 patch.object(check_spec_shapes.subprocess, 'check_output',
                              return_value=retired + '\n' + replacement + '\n') as inventory:
                self.assertEqual(check_spec_shapes.main(), 0)
                self.assertIn('--others', inventory.call_args.args[0])

    def test_inventory_checks_all_four_shapes_in_both_scopes(self):
        for scope in ("Evidence", "Compliance"):
            with self.subTest(scope=scope), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                name = "ZesuSsz/" + scope + "/Added.v"
                source = root / name
                source.parent.mkdir(parents=True)
                source.write_text("Definition badCallSpec (P : iProp Sigma) : iProp Sigma := "
                                  "(∃ (x : Z), ⌜x = 0⌝ ∗ True ∨ P)%I.")
                baseline = root / "baseline.json"
                baseline.write_text("{}")
                inventory = root / "inventory.json"
                inventory.write_text(json.dumps({"base_commit": "base", "modules": {name: {}}}))
                with patch.object(check_spec_shapes, "ROOT", root), \
                     patch.object(check_spec_shapes, "BASELINE", baseline), \
                     patch.object(check_spec_shapes, "INVENTORY", inventory), \
                     patch.object(check_spec_shapes.subprocess, "check_output", return_value=name), \
                     contextlib.redirect_stderr(io.StringIO()) as errors:
                    self.assertEqual(check_spec_shapes.main(), 1)
                for metric in ("uninferable_existentials", "predicates_without_unfold",
                               "disjunctive_specs", "frame_parameters_in_closed_specs"):
                    self.assertIn(metric + ": 1 > 0", errors.getvalue())

    def test_inventory_rejects_a_missing_added_module(self):
        name = "ZesuSsz/Evidence/New.v"
        with patch.object(check_spec_shapes.subprocess, "check_output", side_effect=[name, ""]):
            errors = check_spec_shapes.scoped_inventory_errors(
                {"base_commit": "base", "modules": {}}, {name: ""})
        self.assertEqual(errors, ["Missing shape inventory: " + name])

    def test_inventory_keeps_preexisting_modules_outside_scope(self):
        old = "ZesuSsz/Evidence/Old.v"
        with patch.object(check_spec_shapes.subprocess, "check_output", side_effect=["", ""]):
            errors = check_spec_shapes.scoped_inventory_errors(
                {"base_commit": "base", "modules": {}}, {old: ""})
        self.assertEqual(errors, [])

    def test_untyped_existential_binders_are_counted(self):
        spec = ('Definition exact : iProp Sigma := '
                '(∃ ret bytes, "x1" ↦ᵣ RVal_Bits ret ∗ '
                '⌜length bytes = 8⌝ ∗ True)%I.')
        self.assertEqual(existential_binders(definitions(spec)[0][2]),
                         ["ret", "bytes"])
        self.assertEqual(shape_counts(spec, {"exact"})[
            "uninferable_existentials"], 1)

    def test_mixed_existential_binders_keep_order(self):
        body = '(∃ first (second third : Z) fourth, True)%I.'
        self.assertEqual(existential_binders(body),
                         ["first", "second", "third", "fourth"])

    def test_unparenthesized_typed_binder_excludes_its_type(self):
        body = '(∃ outcome : DecodeItemOutcome, hidden_resource outcome)%I.'
        self.assertEqual(existential_binders(body), ["outcome"])

    def test_register_binder_is_inferable_before_pure_use(self):
        spec = ('Definition exact `{!islaG Sigma} : iProp Sigma := '
                '(∃ (ret : bv 64), "x1" ↦ᵣ RVal_Bits ret ∗ '
                '⌜bv_unsigned ret = 0⌝ ∗ True)%I.')
        counts = shape_counts(spec, {"exact"})
        self.assertEqual(counts["uninferable_existentials"], 0)

    def test_hidden_register_binder_is_under_function(self):
        spec = ('Definition exact : iProp Sigma := '
                '(∃ (ret : Z), "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 ret) ∗ '
                'True)%I.')
        self.assertEqual(shape_counts(spec, {"exact"})[
            "uninferable_existentials"], 1)
        self.assertEqual(binder_shape("ret", resource_parts(definitions(spec)[0][2]),
                                      {"exact"}), "under_function")

    def test_array_and_trace_tail_binders_are_inferable(self):
        spec = ('Definition exact : iProp Sigma := '
                '(∃ (bytes : list (bv 8)) (tail : spec), '
                'base ↦ₘ∗ bytes ∗ '
                'spec_trace (writeOutputEvents address size payload tail) ∗ '
                'True)%I.')
        self.assertEqual(existential_binders(definitions(spec)[0][2]),
                         ["bytes", "tail"])
        self.assertEqual(shape_counts(spec, {"exact"})[
            "uninferable_existentials"], 0)

    def test_direct_trace_tail_is_inferable(self):
        spec = ('Definition exact : iProp Sigma := '
                '(∃ (tail : spec), spec_trace tail ∗ True)%I.')
        self.assertEqual(shape_counts(spec, {"exact"})[
            "uninferable_existentials"], 0)

    def test_memory_address_binder_is_inferable(self):
        spec = ('Definition exact : iProp Sigma := '
                '(∃ (base : Z), base ↦ₘ? 8 ∗ True)%I.')
        self.assertEqual(shape_counts(spec, {"exact"})[
            "uninferable_existentials"], 0)

    def test_pure_first_occurrence_does_not_infer_memory(self):
        spec = ('Definition exact : iProp Sigma := '
                '(∃ (bytes : list (bv 8)), '
                '⌜length bytes = 8⌝ ∗ base ↦ₘ∗ bytes ∗ True)%I.')
        self.assertEqual(shape_counts(spec, {"exact"})[
            "uninferable_existentials"], 1)
        self.assertEqual(binder_shape("bytes", resource_parts(definitions(spec)[0][2]),
                                      {"exact"}), "pure_only")

    def test_spatial_predicate_infers_binder_before_all_pure_facts(self):
        for body, expected in (
            ('exit_resources args outcome ∗ ⌜meaning args outcome⌝', 0),
            ('⌜meaning args outcome⌝ ∗ exit_resources args outcome', 1),
            ('exit_resources args outcome ∗ ⌜domain outcome⌝ ∗ '
             '⌜meaning args outcome⌝', 0),
            ('⌜domain outcome⌝ ∗ exit_resources args outcome ∗ '
             '⌜meaning args outcome⌝', 1),
            ('unrelated_resources args ∗ ⌜meaning args outcome⌝', 1),
            ('(exit_resources args outcome)%I ∗ ⌜meaning args outcome⌝', 0),
            ('(exit_resources outcome ∗ ⌜meaning outcome⌝)', 0),
            ('((exit_resources outcome ∗ ⌜meaning outcome⌝))', 0),
            ('exit_resources (outcome) ∗ ⌜meaning outcome⌝', 0),
            ('exit_resources ((outcome)) ∗ ⌜meaning outcome⌝', 0),
            ('(exit_resources outcome ∗ ⌜meaning outcome⌝) ∗ True', 0),
            ('exit_resources outcome ∗ (⌜domain outcome⌝ ∗ '
             '⌜meaning outcome⌝)', 0),
            ('((⌜meaning outcome⌝ ∗ exit_resources outcome))', 1),
        ):
            with self.subTest(body=body):
                spec = ('Definition exact : iProp Sigma := '
                        '(∃ outcome : Outcome, ' + body + ')%I.')
                self.assertEqual(shape_counts(spec, {"exact"})[
                    "uninferable_existentials"], expected)

    def test_resources_first_does_not_cross_nested_boundaries(self):
        for body in (
            'instr_pre pc (exit_resources outcome ∗ ⌜meaning outcome⌝)',
            'exit_resources (transform outcome) ∗ ⌜meaning outcome⌝',
            'exit_resources ((transform (outcome))) ∗ ⌜meaning outcome⌝',
            '(∃ inner, exit_resources outcome inner) ∗ ⌜meaning outcome⌝',
            'exit_resources outcome -∗ ⌜meaning outcome⌝',
            'exit_resources outcome ∗ ⌜meaning outcome⌝ ∨ True',
            'exit_resources outcomes ∗ ⌜meaning outcome⌝',
            'exit_resources Constants.outcome ∗ ⌜meaning outcome⌝',
            'exit_resources "outcome" ∗ ⌜meaning outcome⌝',
        ):
            with self.subTest(body=body):
                spec = ('Definition exact : iProp Sigma := '
                        '(∃ outcome : Outcome, ' + body + ')%I.')
                self.assertEqual(shape_counts(spec, {"exact"})[
                    "uninferable_existentials"], 1)

    def test_resources_first_is_local_to_the_existential_conjunction(self):
        nested = ('Definition exact : iProp Sigma := '
                  'instr_pre pc (∃ outcome : Outcome, '
                  'exit_resources outcome ∗ ⌜meaning outcome⌝).')
        outside = ('Definition exact (outcome : Outcome) : iProp Sigma := '
                   '((∃ outcome : Outcome, hidden_resource outcome) ∗ '
                   '⌜meaning outcome⌝)%I.')
        self.assertEqual(shape_counts(nested, {"exact"})[
            "uninferable_existentials"], 0)
        self.assertEqual(shape_counts(outside, {"exact"})[
            "uninferable_existentials"], 1)

    def test_opaque_resource_and_disjunction_are_counted(self):
        spec = ('Definition exact : iProp Sigma := '
                '(∃ (ret : bv 64), hidden_resource ret ∗ True ∨ False)%I.')
        counts = shape_counts(spec, set())
        self.assertEqual(counts["predicates_without_unfold"], 1)
        self.assertEqual(counts["disjunctive_specs"], 1)
        self.assertEqual(counts["uninferable_existentials"], 1)
        self.assertEqual(binder_shape("ret", resource_parts(definitions(spec)[0][2]),
                                      set()), "opaque_predicate")

    def test_closed_spec_frame_is_counted(self):
        spec = ('Definition exactCallSpec (P : iProp Sigma) '
                ': iProp Sigma := (instr_pre ret P ∗ True)%I.')
        self.assertEqual(shape_counts(spec, {"exactCallSpec"})[
            "frame_parameters_in_closed_specs"], 1)

    def test_sealed_predicate_satisfies_unfold_metric(self):
        sealed = ('Definition exact : iProp Sigma := (True)%I.\n'
                  'Lemma exact_unfold : exact ⊣⊢ (True)%I.\n'
                  'Proof. done. Qed.\n'
                  'Global Opaque exact.')
        missing_lemma = ('Definition hidden : iProp Sigma := (True)%I.\n'
                         'Global Opaque hidden.')
        self.assertEqual(shape_counts(sealed, set())[
            "predicates_without_unfold"], 0)
        self.assertEqual(shape_counts(missing_lemma, set())[
            "predicates_without_unfold"], 1)

    def test_nested_comments_do_not_create_specs(self):
        spec = ('(* Definition fake : iProp Sigma := (True ∨ False)%I. '
                '(* nested ∃ (ghost : nat) *) *) '
                'Definition exact : iProp Sigma := (True)%I.')
        counts = shape_counts(spec, {"exact"})
        self.assertEqual(counts["disjunctive_specs"], 0)
        self.assertEqual(counts["uninferable_existentials"], 0)

    def test_new_file_has_zero_baseline(self):
        count = dict(uninferable_existentials=1,
                     predicates_without_unfold=0,
                     disjunctive_specs=0,
                     frame_parameters_in_closed_specs=0)
        self.assertEqual(len(failures("new.v", count, {})), 1)
        self.assertEqual(failures("old.v", count, {"old.v": count}), [])

    def test_unfold_instances_require_explicit_typeclass_opacity(self):
        for scope in ("Global", "Local", "#[local]", "#[global]", ""):
            with self.subTest(scope=scope):
                source = f'{scope} Instance : LithiumUnfold (@callSpec) := I.'
                self.assertEqual(unfold_opacity_count(source, set()), 1)
                opaque = typeclasses_opaque('Global Typeclasses Opaque callSpec.')
                self.assertEqual(unfold_opacity_count(source, opaque), 0)
                self.assertEqual(typeclasses_opaque('Global Opaque callSpec.'), set())

    def test_unfold_targets_include_named_multiline_and_qualified_instances(self):
        source = ('#[local] Instance call_unfold `{!islaG Sigma} :\n'
                  '  LithiumUnfold (@Calls.callSpec) := I.\n'
                  'Global Instance ret_unfold : LithiumUnfold returnSpec := I.')
        self.assertEqual(unfold_targets(source), ['Calls.callSpec', 'returnSpec'])

    def test_unfold_targets_include_proof_bodies_and_priorities(self):
        source = ('Global Instance : LithiumUnfold (@callSpec).\n'
                  'Proof. exact I. Qed.\n'
                  'Local Instance : LithiumUnfold (@returnSpec) | 10 := I.')
        self.assertEqual(unfold_targets(source), ['callSpec', 'returnSpec'])
        self.assertEqual(unfold_opacity_count(source, {'returnSpec'}), 1)

    def test_typeclass_opacity_supports_lists_and_locality(self):
        source = ('Global\nTypeclasses Opaque callSpec Calls.returnSpec.\n'
                  '#[global] Typeclasses Opaque frameSpec.\n'
                  '#[export] Typeclasses Opaque Exported.entry.\n'
                  'Local Typeclasses Opaque localSpec.\n'
                  '#[local] Typeclasses Opaque anotherLocal.\n'
                  'Typeclasses Opaque defaultSpec.')
        self.assertEqual(typeclasses_opaque(source, global_only=True),
                         {'callSpec', 'Calls.returnSpec', 'frameSpec', 'Exported.entry'})
        self.assertEqual(typeclasses_opaque(source),
                         {'callSpec', 'Calls.returnSpec', 'frameSpec', 'Exported.entry',
                          'localSpec', 'anotherLocal', 'defaultSpec'})

    def test_comments_do_not_supply_opacity_or_instances(self):
        source = ('(* Global Typeclasses Opaque callSpec. (* nested *) *)\n'
                  'Global Instance : LithiumUnfold (@callSpec) := I.\n'
                  '(* Global Instance : LithiumUnfold (@fakeSpec) := I. *)')
        self.assertEqual(unfold_targets(source), ['callSpec'])
        self.assertEqual(unfold_opacity_count(source, typeclasses_opaque(source)), 1)

    def test_nonconstant_unfold_target_is_a_violation(self):
        source = 'Global Instance : LithiumUnfold (fun x => x) := I.'
        self.assertEqual(unfold_targets(source), [None])
        self.assertEqual(unfold_opacity_count(source, {'x'}), 1)

    def test_call_body_opacity_does_not_seal_the_instance_constant(self):
        source = ('Definition callSpec : iProp Sigma := zesu_call 16 P.\n'
                  'Global Instance : LithiumUnfold (@callSpec) := I.\n'
                  'Global Typeclasses Opaque zesu_call zesu_call_ret.')
        count = unfold_opacity_count(source, typeclasses_opaque(source))
        self.assertEqual(count, 1)
        counts = {'unfold_without_typeclasses_opaque': count}
        self.assertEqual(failures('old.v', counts, {'old.v': counts}), [])
        self.assertEqual(failures('old.v', {'unfold_without_typeclasses_opaque': 2},
                                  {'old.v': counts}),
                         ['old.v: unfold_without_typeclasses_opaque: 2 > 1'])
        self.assertEqual(failures('new.v', counts, {}),
                         ['new.v: unfold_without_typeclasses_opaque: 1 > 0'])

    def test_main_checks_automation_and_preserves_opacity_locality(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            automation = 'ZesuSsz/Automation/Calls.v'
            opacity = 'ZesuSsz/Contracts/Opacity.v'
            (root / automation).parent.mkdir(parents=True)
            (root / opacity).parent.mkdir(parents=True)
            baseline = root / 'baseline.json'
            baseline.write_text(json.dumps({}))
            inventory_file = root / 'inventory.json'
            inventory_file.write_text(json.dumps({'base_commit': 'base', 'modules': {}}))
            with patch.object(check_spec_shapes, 'ROOT', root), \
                 patch.object(check_spec_shapes, 'BASELINE', baseline), \
                 patch.object(check_spec_shapes, 'INVENTORY', inventory_file), \
                 patch.object(check_spec_shapes.subprocess, 'check_output',
                              return_value=automation + '\n' + opacity + '\n'):
                for target in ('callSpec', 'ZesuSsz.Contracts.Opacity.callSpec'):
                    (root / automation).write_text(
                        'Definition callSpec := 1.\n'
                        f'Global Instance : LithiumUnfold (@{target}) := I.')
                    for scope in ('Global', '#[global]', '#[export]', 'Local', '#[local]'):
                        with self.subTest(target=target, scope=scope):
                            (root / opacity).write_text(
                                'Definition callSpec := 2.\n'
                                f'{scope} Typeclasses Opaque callSpec.')
                            expected = int(target == 'callSpec' or
                                           scope in ('Local', '#[local]'))
                            with contextlib.redirect_stderr(io.StringIO()) as errors:
                                self.assertEqual(check_spec_shapes.main(), expected)
                            if expected:
                                self.assertIn(automation + ': unfold_without_typeclasses_opaque: 1 > 0',
                                              errors.getvalue())
                (root / automation).write_text(
                    'Global Instance : LithiumUnfold (@callSpec) := I.\n'
                    'Local Typeclasses Opaque callSpec.')
                with contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(check_spec_shapes.main(), 0)


class QualifiedUnfoldTests(unittest.TestCase):
    def test_qualified_target_matches_only_its_defining_module(self):
        source = 'Definition exact : iProp Sigma := True%I.\n'
        for targets, module, missing in [
            ({'ZesuSsz.Contracts.First.exact'}, 'ZesuSsz.Contracts.First', 0),
            ({'ZesuSsz.Contracts.Second.exact'}, 'ZesuSsz.Contracts.First', 1),
            ({'ZesuSsz.Contracts.Outer.First.exact'}, 'ZesuSsz.Contracts.First', 1),
            ({'ZesuSsz.Contracts.First.exact'}, 'ZesuSsz.Contracts.Second', 1),
            ({'ZesuSsz.Contracts.First.exact'}, None, 1),
            ({'exact'}, 'ZesuSsz.Contracts.First', 0),
        ]:
            with self.subTest(targets=targets, module=module):
                self.assertEqual(shape_counts(source, targets, module=module)[
                    'predicates_without_unfold'], missing)

    def test_main_refuses_a_foreign_same_name_registration(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = 'ZesuSsz/Contracts/First.v'
            second = 'ZesuSsz/Contracts/Second.v'
            generated = 'ZesuSsz/Generated/Example/BootstrapRegistrations.v'
            sources = {first: 'Definition exact : iProp Sigma := True%I.\n',
                       second: 'Definition exact : iProp Sigma := True%I.\n',
                       generated: 'Global Instance : LithiumUnfold (@ZesuSsz.Contracts.First.exact) := I.\n'
                                  'Global Typeclasses Opaque ZesuSsz.Contracts.First.exact.\n'}
            for name, source in sources.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            baseline = root / 'baseline.json'
            baseline.write_text('{}')
            inventory = root / 'inventory.json'
            inventory.write_text(json.dumps({'base_commit': 'fixture', 'modules': {}}))
            errors = io.StringIO()
            with patch.object(check_spec_shapes, 'ROOT', root), \
                    patch.object(check_spec_shapes, 'BASELINE', baseline), \
                    patch.object(check_spec_shapes, 'INVENTORY', inventory), \
                    patch.object(check_spec_shapes, 'scoped_inventory_errors', return_value=[]), \
                    patch.object(check_spec_shapes.subprocess, 'check_output', return_value='\n'.join(sources)), \
                    contextlib.redirect_stderr(errors):
                self.assertEqual(check_spec_shapes.main(), 1)
            self.assertEqual(errors.getvalue(), second + ': predicates_without_unfold: 1 > 0\n')


if __name__ == "__main__":
    unittest.main()
