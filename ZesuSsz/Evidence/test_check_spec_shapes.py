import contextlib
import io
import json
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
    def test_main_checks_added_replacement_and_skips_deleted_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            replacement = 'ZesuSsz/Proofs/DecodeItem/Auto/Join6ae0From6a38.v'
            retired = 'ZesuSsz/Proofs/DecodeItem/Join6ae0/From6a38.v'
            (root / replacement).parent.mkdir(parents=True)
            (root / replacement).write_text('Lemma covered : True. Proof. exact I. Qed.')
            baseline = root / 'baseline.json'
            baseline.write_text('{}')
            with patch.object(check_spec_shapes, 'ROOT', root), \
                 patch.object(check_spec_shapes, 'BASELINE', baseline), \
                 patch.object(check_spec_shapes.subprocess, 'check_output',
                              return_value=retired + '\n' + replacement + '\n') as inventory:
                self.assertEqual(check_spec_shapes.main(), 0)
                self.assertIn('--others', inventory.call_args.args[0])

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
                  'Local Typeclasses Opaque localSpec.\n'
                  '#[local] Typeclasses Opaque anotherLocal.\n'
                  'Typeclasses Opaque defaultSpec.')
        self.assertEqual(typeclasses_opaque(source, global_only=True),
                         {'callSpec', 'Calls.returnSpec', 'frameSpec'})
        self.assertEqual(typeclasses_opaque(source),
                         {'callSpec', 'Calls.returnSpec', 'frameSpec',
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
            with patch.object(check_spec_shapes, 'ROOT', root), \
                 patch.object(check_spec_shapes, 'BASELINE', baseline), \
                 patch.object(check_spec_shapes.subprocess, 'check_output',
                              return_value=automation + '\n' + opacity + '\n'):
                for target in ('callSpec', 'ZesuSsz.Contracts.Opacity.callSpec'):
                    (root / automation).write_text(
                        'Definition callSpec := 1.\n'
                        f'Global Instance : LithiumUnfold (@{target}) := I.')
                    for scope in ('Global', '#[global]', 'Local', '#[local]'):
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


if __name__ == "__main__":
    unittest.main()
