From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRegisterUpdate.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPrefixDestinationUnsigned sp :
  bv_unsigned sp + 1792 < 0x40000000 ->
  bv_unsigned (sp + BV 64 1744)%bv = bv_unsigned sp + 1744.
Proof.
  intros Hupper. rewrite bv_add_unsigned bv_unsigned_BV. cbn.
  unfold bv_wrap, bv_modulus. cbn. rewrite Z.mod_small; first reflexivity.
  pose proof (bv_unsigned_in_range 64 sp). unfold bv_modulus in *. cbn in *.
  lia.
Qed.

Definition writeSuccessWithdrawalsPrefixRegs regs sp pointer : reg_map :=
  writeSuccess156a4Regs
    (writeSuccess156a0Regs
      (writeSuccess1569cRegs
        (writeSuccess15698Regs (writeSuccess15694Regs regs sp)) pointer)).

Lemma writeSuccessWithdrawalsPrefixAfterShape machine sp pointer :
  (writeSuccessWithdrawalsPrefixAfter machine sp pointer).1.(seq_regs) =
    writeSuccessWithdrawalsPrefixRegs machine.1.(seq_regs) sp pointer /\
  (writeSuccessWithdrawalsPrefixAfter machine sp pointer).2 = machine.2.
Proof. split; reflexivity. Qed.

Lemma writeSuccessWithdrawalsPrefixRegsPc regs sp pointer :
  writeSuccessWithdrawalsPrefixRegs regs sp pointer !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x101d4)).
Proof.
  unfold writeSuccessWithdrawalsPrefixRegs, writeSuccess156a4Regs.
  rewrite lookup_insert. pose proof writeSuccess156a4ValuesExact as (_ & _ & _ & H).
  rewrite H. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsPrefixRegsX1 regs sp pointer :
  writeSuccessWithdrawalsPrefixRegs regs sp pointer !! "x1" =
    Some (RVal_Bits (Z_to_bv 64 0x156a8)).
Proof.
  unfold writeSuccessWithdrawalsPrefixRegs, writeSuccess156a4Regs.
  rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
  pose proof writeSuccess156a4ValuesExact as (_ & H & _). rewrite H. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsPrefixRegsX10 regs sp pointer :
  writeSuccessWithdrawalsPrefixRegs regs sp pointer !! "x10" =
    Some (RVal_Bits (sp + BV 64 1744)%bv).
Proof.
  unfold writeSuccessWithdrawalsPrefixRegs.
  rewrite writeSuccess156a4RegsLookupOther; try discriminate.
  rewrite writeSuccess156a0RegsLookupOther; try discriminate.
  rewrite writeSuccess1569cRegsLookupOther; try discriminate.
  rewrite writeSuccess15698RegsLookupOther; try discriminate.
  unfold writeSuccess15694Regs. rewrite lookup_insert_ne; last discriminate.
  rewrite lookup_insert. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsPrefixRegsX11 regs sp pointer :
  writeSuccessWithdrawalsPrefixRegs regs sp pointer !! "x11" =
    Some (RVal_Bits pointer).
Proof.
  unfold writeSuccessWithdrawalsPrefixRegs.
  rewrite writeSuccess156a4RegsLookupOther; try discriminate.
  rewrite writeSuccess156a0RegsLookupOther; try discriminate.
  unfold writeSuccess1569cRegs. rewrite lookup_insert_ne; last discriminate.
  rewrite lookup_insert. replace (pointer + BV 64 0)%bv with pointer; first reflexivity.
  apply bv_eq. bv_solve.
Qed.

Lemma writeSuccessWithdrawalsPrefixRegsX12 regs sp pointer :
  writeSuccessWithdrawalsPrefixRegs regs sp pointer !! "x12" =
    Some (RVal_Bits (BV 64 48)).
Proof.
  unfold writeSuccessWithdrawalsPrefixRegs.
  rewrite writeSuccess156a4RegsLookupOther; try discriminate.
  rewrite writeSuccess156a0RegsLookupOther; try discriminate.
  rewrite writeSuccess1569cRegsLookupOther; try discriminate.
  unfold writeSuccess15698Regs. rewrite lookup_insert_ne; last discriminate.
  rewrite lookup_insert. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsPrefixRegsOperationalFacts regs sp pointer :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessWithdrawalsPrefixRegs regs sp pointer).
Proof.
  intros Hfacts. unfold writeSuccessWithdrawalsPrefixRegs,
    writeSuccess156a4Regs, writeSuccess156a0Regs, writeSuccess1569cRegs,
    writeSuccess15698Regs, writeSuccess15694Regs.
  repeat (apply writeSuccessOperationalRegisterFactsInsertBit;
    [|discriminate|vm_compute; repeat constructor; discriminate|
      cbn; intuition congruence]).
  exact Hfacts.
Qed.

Lemma writeSuccessWithdrawalsPrefixAfterBoundary machine sp pointer :
  writeSuccessWithdrawalsInstructionTable machine.2 ->
  IslaInstructionBoundary (writeSuccessWithdrawalsPrefixAfter machine sp pointer).
Proof.
  intros Htable. split; first reflexivity.
  exists (Z_to_bv 64 0x101d4), a101d4. repeat split.
  - change (writeSuccessWithdrawalsPrefixRegs machine.1.(seq_regs) sp pointer !!
      "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d4))).
    apply writeSuccessWithdrawalsPrefixRegsPc.
  - apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefixAfterShape.
Print Assumptions writeSuccessWithdrawalsPrefixDestinationUnsigned.
Print Assumptions writeSuccessWithdrawalsPrefixRegsPc.
Print Assumptions writeSuccessWithdrawalsPrefixRegsX1.
Print Assumptions writeSuccessWithdrawalsPrefixRegsX10.
Print Assumptions writeSuccessWithdrawalsPrefixRegsX11.
Print Assumptions writeSuccessWithdrawalsPrefixRegsX12.
Print Assumptions writeSuccessWithdrawalsPrefixRegsOperationalFacts.
Print Assumptions writeSuccessWithdrawalsPrefixAfterBoundary.
