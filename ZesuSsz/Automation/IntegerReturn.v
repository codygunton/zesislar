Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Automation.Rewrites.

Class ZesuStepIntegerReturn : Prop := zesu_step_integer_return : True.

Lemma zesu_return_fault_bit_from_extracts (ret : bv 64) :
  bv_extract 0 1 ret = BV 1 0 ->
  bv_extract 1 1 ret = BV 1 0 ->
  bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add ret (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 0.
Proof.
 intros Hlow Hhigh.
 assert (Hmasked : bv_or (bv_and (bv_add ret (BV 64 0))
   (BV 64 18446744073709551614)) (BV 64 0) = ret).
 { apply bv_eq.
   pose proof (normalize_instr_addr_riscv64_ret_tac ret _ Hlow eq_refl) as Hnormalized.
   rewrite !bv_wrap_bv_unsigned in Hnormalized. exact Hnormalized. }
 rewrite Hmasked. apply bv_eq.
 rewrite bv_extract_0_unsigned bv_shiftr_unsigned.
 change (bv_wrap 1 (bv_unsigned ret ≫ 1) = 0).
 pose proof (f_equal (@bv_unsigned 1) Hhigh) as Hbit.
 rewrite bv_extract_unsigned in Hbit. exact Hbit.
Qed.
Ltac zesu_return_integer_range R continuation :=
  assert_fails (has_evar R);
  zesu_integer_array_facts;
  try autounfold with zesu_contract_constants in *;
  match goal with
  | Hlower : (0 <= R)%Z,
    Hupper : (R < 2 ^ 64)%Z,
    Haligned : (R mod 4 = 0)%Z |- _ =>
      continuation Hlower Hupper Haligned
  end.

Lemma zesu_ret_target (R : Z) :
  (R mod 2 = 0)%Z ->
  bv_wrap 64 (bv_unsigned
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 0xfffffffffffffffe)) (BV 64 0))) = bv_wrap 64 R.
Proof.
  intro Heven.
  assert (Hlow : bv_extract 0 1 (Z_to_bv 64 R) = BV 1 0) by bv_solve.
  apply (normalize_instr_addr_riscv64_ret_tac (Z_to_bv 64 R) _ Hlow).
  rewrite Z_to_bv_unsigned. apply bv_wrap_bv_wrap. apply N.le_refl.
Qed.

(* Inspect one local target alias before the context-wide LET expansion. *)
Ltac zesu_return_masked_head target :=
  lazymatch target with
  | bv_or (bv_and _ _) _ => idtac
  | _ =>
      is_var target;
      let exposed := eval cbv delta [target] in target in
      lazymatch exposed with
      | bv_or (bv_and _ _) _ => idtac
      end
  end.

(* Inspect only the selected bit alias and its selected address alias. *)
Ltac zesu_return_fault_bit_head bit :=
  let inspect exposed :=
    lazymatch exposed with
    | bv_extract 0 1 (bv_shiftr ?target _) =>
        zesu_return_masked_head target
    end in
  first [inspect bit | is_var bit;
    let exposed := eval cbv delta [bit] in bit in inspect exposed].

Ltac zesu_return_integer_normalize :=
  lazymatch goal with
  | |- LiTactic (normalize_instr_addr (bv_unsigned ?target)) =>
      zesu_return_masked_head target
  end;
  zesu_switch_enabled constr:(ZesuStepIntegerReturn);
  unLET;
  lazymatch goal with
  | |- LiTactic (normalize_instr_addr
      (bv_unsigned (bv_or (bv_and (bv_add (Z_to_bv 64 ?R) (BV 64 0))
        (BV 64 0xfffffffffffffffe)) (BV 64 0)))) =>
      assert_fails (has_evar R);
      zesu_integer_array_facts;
      let Heven := fresh "HreturnEven" in
      assert (Heven : (R mod 2 = 0)%Z) by
        first [assumption | match goal with H : (R mod 4 = 0)%Z |- _ => lia end];
      exact (normalize_instr_addr_hint _ R (zesu_ret_target R Heven))
  end.

Ltac zesu_return_integer_fault :=
  lazymatch goal with
  | |- SimplImpl (@eq _ ?bit _) _ =>
      zesu_return_fault_bit_head bit
  end;
  zesu_switch_enabled constr:(ZesuStepIntegerReturn);
  unLET;
  lazymatch goal with
  | |- SimplImpl (bv_extract 0 1 (bv_shiftr
      (bv_or (bv_and (bv_add (Z_to_bv 64 ?R) (BV 64 0))
        (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) ?Q =>
    zesu_return_integer_range R ltac:(fun Hlower Hupper Haligned =>
      let Hlow := fresh "HreturnLowBit" in
      let Hhigh := fresh "HreturnHighBit" in
      assert (Hlow : bv_extract 0 1 (Z_to_bv 64 R) = BV 1 0) by
        (clear -Hlower Hupper Haligned; bv_solve);
      assert (Hhigh : bv_extract 1 1 (Z_to_bv 64 R) = BV 1 0) by
        (clear -Hlower Hupper Haligned; bv_solve);
      unify Q False; unfold SimplImpl; split; [intros [] |];
      let Hfault := fresh "Hfault" in intro Hfault;
      rewrite (zesu_return_fault_bit_from_extracts (Z_to_bv 64 R) Hlow Hhigh) in Hfault;
      discriminate)
  end.

#[export] Hint Extern 5 (LiTactic (normalize_instr_addr _)) =>
  zesu_return_integer_normalize : typeclass_instances.
#[export] Hint Extern 5 (SimplImpl _ _) =>
  zesu_return_integer_fault : typeclass_instances.


(* Clearing an already-zero low bit preserves the complete word. *)
Lemma zesu_bv64_clear_low_bit_even (value : bv 64) :
  (bv_unsigned value mod 2 = 0)%Z ->
  bv_and value (BV 64 18446744073709551614) = value.
Proof.
 intro Heven.
 assert (Hlow : bv_extract 0 1 value = BV 1 0).
 { apply bv_eq. rewrite bv_extract_0_unsigned.
   change (bv_unsigned value mod 2 = 0)%Z. exact Heven. }
 apply bv_eq.
 pose proof (normalize_instr_addr_riscv64_ret_tac value _ Hlow eq_refl) as Hnormalized.
 rewrite !bv_wrap_bv_unsigned in Hnormalized.
 rewrite (bv_add_0_r value (BV 64 0) eq_refl) in Hnormalized.
 rewrite (bv_or_0_r (bv_and value (BV 64 18446744073709551614)) (BV 64 0) eq_refl) in Hnormalized.
 exact Hnormalized.
Qed.

(* Inspect the requested low-bit mask before using existing integer bounds. *)
Ltac zesu_return_integer_even_mask :=
  lazymatch goal with
  | |- context [bv_and ?value (BV 64 18446744073709551614)] =>
      assert_fails (has_evar value);
      let Heven := fresh "HreturnWordEven" in
      assert (Heven : (bv_unsigned value mod 2 = 0)%Z) by (
        first [assumption |
          lazymatch value with
          | Z_to_bv 64 ?integer =>
              let Hrange := fresh "HreturnIntegerRange" in
              assert (Hrange : (0 <= integer < 2 ^ 64)%Z) by lia;
              rewrite Z_to_bv_unsigned;
              rewrite (bv_wrap_small 64 integer Hrange);
              match goal with
              | Haligned : (integer mod 4 = 0)%Z |- _ => lia
              end
          end]);
      rewrite (zesu_bv64_clear_low_bit_even value Heven);
      clear Heven;
      repeat match goal with
      | |- context [bv_or ?word (BV 64 0)] =>
          rewrite (bv_or_0_r word (BV 64 0) eq_refl)
      end;
      try (lazymatch value with
      | Z_to_bv 64 ?integer =>
          let Hrange := fresh "HreturnIntegerRange" in
          assert (Hrange : (0 <= integer < 2 ^ 64)%Z) by lia;
          rewrite (Z_to_bv_unsigned 64 integer);
          rewrite (bv_wrap_small 64 integer Hrange);
          clear Hrange
      end)
  end.
