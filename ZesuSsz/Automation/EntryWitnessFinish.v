Require Import ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.ByteMaskCast.
Require Import ZesuSsz.Evidence.EntryWitnessInputs.
Require Import ZesuSsz.Evidence.EntryWitnessSelector.
From iris.proofmode Require Import environments.
From lithium Require Import pure_definitions.
From Coq Require Import ZArith Lia.
From stdpp Require Import bitvector.tactics.
Local Open Scope Z_scope.

(* Reuse the proved byte cast and one-wrap family. No source fact is added. *)
Ltac zesu_byte_bias_finish :=
  solve [lazymatch goal with
  | |- context [bv_and (bv_add (bv_and (bv_sign_extend ?width ?word) ?mask) ?offset) ?mask] =>
      is_closed_term width; is_closed_term mask; is_closed_term offset;
      assert_fails (has_evar word);
      lazymatch type of word with bv 8%N => idtac end;
      let integer := eval vm_compute in (bv_unsigned offset) in
      let modulus := eval vm_compute in (bv_modulus 8) in
      let Hwidth := fresh "HbyteBiasWidth" in
      assert (Hwidth : (8 <= width)%N) by (vm_compute; congruence);
      let Hmask := fresh "HbyteBiasMask" in
      assert (Hmask : mask = Z_to_bv width (2 ^ 8 - 1)) by
        (apply bv_eq; vm_compute; reflexivity);
      let Hcast := fresh "HbyteBiasCast" in
      assert (Hcast : bv_unsigned (Z_to_bv width (bv_unsigned word)) = bv_unsigned word) by
        (apply Z_to_bv_small;
         pose proof (bv_unsigned_in_range 8 word);
         pose proof (bv_modulus_le_mono 8 width Hwidth); lia);
      let Hresult := fresh "HbyteBiasPresentation" in
      assert (Hresult : bv_and (bv_add (bv_and (bv_sign_extend width word) mask) offset) mask =
          Z_to_bv width (bv_unsigned word + integer - modulus)) by
        (rewrite Hmask;
         rewrite (ByteMaskCast.zesu_sign_extended_byte_mask width word Hwidth);
         Hooks.zesu_low_mask_bv_goal);
      rewrite Hresult;
      bv_solve
  end].

(* A bounded transition delegates witness choice to the unchanged selector. *)
Ltac zesu_entry_finish_phase fuel step :=
  lazymatch fuel with
  | O => fail 0 "The registered witness phase did not become ready."
  | S ?remaining =>
      first [EntryWitnessInputs.zesu_entry_mapping_consume_ready |
             progress step; zesu_entry_finish_phase remaining step]
  end.

(* Call explicitly after native search. No hook or registration is replaced. *)
Ltac zesu_entry_witness_finish step scalar :=
  lazymatch goal with
  | _ : @ZesuEntryWitnessPending _ _ _ _ |- environments.envs_entails _ _ =>
      solve [try progress (rewrite -isla.ghost_state.mem_mapsto_array_eq);
             zesu_entry_finish_phase constr:(64%nat) step;
             iFrame; repeat iSplit; iPureIntro; scalar]
  end.
