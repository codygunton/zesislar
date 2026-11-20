Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A load inside an array of Sail bytes (`bv (Z_idx 8)`, a callee's result
   list), the access address a chain of closed offsets on the stack word and
   the owner's address integer arithmetic over it: Lithium's array lookup
   finds the array and hands its own list to the continuation. *)
Lemma element_width_array_lookup `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (bytes : list (bv (MachineWord.Z_idx 8))) :
  2684355072 <= bv_unsigned sp -> bv_unsigned sp < 3221225472 ->
  length bytes = 16%nat ->
  (bv_unsigned sp - 400 + 48 + 56 + 40) ↦ₘ∗ bytes -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400
      + BV 64 18446744073709551368)))
    (fun mk => match mk with
      | MKArray _ a' values => ⌜(a' = bv_unsigned sp - 256)%Z /\ length values = 16%nat⌝
      | _ => False end)%I.
Proof.
  intros Hlo Hhi Hlength. iIntros "Hbytes".
  liStep.
  iPureIntro. split; [lia | exact Hlength].
Qed.

(* The side condition of that lookup: the stride `Z.of_N (Z_idx 8 / 8)` and
   the `length` atom on Sail bytes; the length fact counts at the same type.
   `bv_solve` computes the widths in goal and context together. *)
Lemma element_width_side_condition (sp : bv 64) (bytes : list (bv (MachineWord.Z_idx 8))) :
  2684355072 <= bv_unsigned sp -> bv_unsigned sp < 3221225472 ->
  length bytes = 16%nat ->
  bv_unsigned sp - 256 <= bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400
      + BV 64 18446744073709551368) <
    bv_unsigned sp - 256 + length bytes * Z.of_N (MachineWord.Z_idx 8 / 8).
Proof.
  intros Hlo Hhi Hlength.
  bv_solve.
Qed.

(* The width step runs on a goal that mentions `Z_idx` and computes it in the
   context as well; a goal without `Z_idx` is refused. *)
Lemma element_width_alias_fires (bytes : list (bv (MachineWord.Z_idx 8))) :
  length bytes = 16%nat -> Z.of_N (MachineWord.Z_idx 8 / 8) = 1.
Proof.
  intros Hlength.
  ZesuSsz.Automation2.Hooks.zesu_finish_element_alias.
  lazymatch type of Hlength with @length (bv 8) _ = _ => idtac end.
  reflexivity.
Qed.

Lemma element_width_alias_refuses_plain (bytes : list (bv 8)) :
  length bytes = 16%nat -> Z.of_N (8 / 8) = 1.
Proof.
  intros Hlength.
  assert_fails ZesuSsz.Automation2.Hooks.zesu_finish_element_alias.
  idtac "PLAIN_WIDTH_REFUSED".
  reflexivity.
Qed.
