From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalEncoderEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalEncoderEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156dcLoopTailRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIteration410.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRegisterUpdate.

Open Scope Z_scope.

Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsTailRegisterPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsTailBoundary.

Lemma writeSuccessWithdrawalsFinalEncoderTailStatePackage args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
    writeSuccess15d10Before regs2 global2 ->
  writeSuccessWithdrawalsOutputEntry
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
      withdrawal).1.(seq_regs)
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
      withdrawal).2 (sp + BV 64 1768)%bv =
    writeSuccess10190Before outputRegs outputGlobal ->
  writeSuccess156d8After
      (writeSuccess156d4Regs
        (writeSuccess156d0Regs
          (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
          (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal =
    writeSuccess15d10Before finalRegs finalGlobal ->
  let endpoint := writeSuccessWithdrawalsIteration410Endpoint finalRegs
    finalGlobal sp withdrawal in
  let after := writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal
    sp pointer remaining withdrawal in
  IslaInstructionBoundary after /\
  after.1.(seq_pc_reg) = "PC" /\
  writeSuccessWithdrawalsConcretePc (after, []) =
    Some (if Nat.eqb remaining 0 then 0x156e8 else 0x15694) /\
  after.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) /\
  after.1.(seq_regs) !! "x8" = Some (RVal_Bits (pointer + BV 64 48)%bv) /\
  after.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) /\
  after.1.(seq_regs) !! "x18" =
    Some (RVal_Bits (sp + BV 64 1768)%bv) /\
  writeSuccessWithdrawalsOperationalRegisterFacts after.1.(seq_regs) /\
  writeSuccessWithdrawalsRegisterFrame after.1.(seq_regs) registerFrame /\
  writeSuccessWithdrawalsInstructionTable after.2 /\
  after.2 = endpoint.2.
Proof.
  intros Hinv Hp He1 He2 Ho Hfinal. cbn.
  destruct (writeSuccessWithdrawalsFinalEncoderEndpointPreservation args sp
    pointer base total processed (S remaining) withdrawal allBytes prefix
    current suffix scratch encoderScratch registerFrame memoryFrame priorLog
    state regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal
    finalRegs finalGlobal Hinv Hp He1 He2 Ho Hfinal) as
    (Hx2 & Hfacts & Hframe & Hhigh & Hscratch & Hmmio).
  destruct (writeSuccessWithdrawalsFinalEncoderEndpointPackage args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 outputRegs outputGlobal finalRegs
    finalGlobal Hinv Hp He1 He2 Ho Hfinal) as
    (_ & _ & _ & Hx18 & _ & Htable & Hmemory & _).
  have Hx2' := writeSuccessWithdrawalsTailLookupOther
    (writeSuccessWithdrawalsIteration410Endpoint finalRegs finalGlobal sp
      withdrawal).1.(seq_regs)
    (writeSuccessWithdrawalsIteration410Endpoint finalRegs finalGlobal sp
      withdrawal).2 pointer remaining "x2"
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate).
  have Hx18' := writeSuccessWithdrawalsTailLookupOther
    (writeSuccessWithdrawalsIteration410Endpoint finalRegs finalGlobal sp
      withdrawal).1.(seq_regs)
    (writeSuccessWithdrawalsIteration410Endpoint finalRegs finalGlobal sp
      withdrawal).2 pointer remaining "x18"
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate).
  have Hboundary :
      IslaInstructionBoundary
        (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
          pointer remaining withdrawal) /\
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
        pointer remaining withdrawal).1.(seq_pc_reg) = "PC" /\
      writeSuccessWithdrawalsConcretePc
        (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
          pointer remaining withdrawal, []) =
        Some (if Nat.eqb remaining 0 then 0x156e8 else 0x15694).
  { destruct remaining as [|r].
    - cbn. apply writeSuccessWithdrawalsTailBoundaryZero. exact Htable.
    - have Hall : allBytes = prefix ++ current ++ suffix by
        (unfold Inv_15694 in Hinv; tauto).
      have HprefixLength : length prefix = (48 * processed)%nat by
        (unfold Inv_15694 in Hinv; tauto).
      have HcurrentLength : length current = 48%nat by
        (unfold Inv_15694 in Hinv; tauto).
      have HsuffixLength : length suffix = (48 * S r)%nat by
        (unfold Inv_15694 in Hinv; cbn in Hinv; tauto).
      have Hupper : base + Z.of_nat (length allBytes) < 0x40000000 by
        (unfold Inv_15694 in Hinv; tauto).
      have Hlower : 0x20000000 <= base by
        (unfold Inv_15694 in Hinv; tauto).
      have Hlt : Z.of_nat (S r) < 2 ^ 64.
      { rewrite Hall !app_length HprefixLength HcurrentLength HsuffixLength
          in Hupper.
        repeat rewrite Nat2Z.inj_add in Hupper.
        repeat rewrite Nat2Z.inj_mul in Hupper. cbn in Hupper.
        pose proof (Nat2Z.is_nonneg processed). pose proof (Nat2Z.is_nonneg r).
        lia. }
      have Hne : Z_to_bv 64 (Z.of_nat (S r)) <> BV 64 0.
      { intros Hz. have Hu := f_equal bv_unsigned Hz.
        have Hrange : 0 <= Z.of_nat (S r) < bv_modulus 64.
        { unfold bv_modulus. cbn. lia. }
        rewrite Z_to_bv_small in Hu; last exact Hrange.
        change (Z.of_nat (S r) = 0) in Hu. lia. }
      cbn. apply writeSuccessWithdrawalsTailBoundaryNonzero; assumption. }
  unfold writeSuccessWithdrawalsIteration410Machine. cbn.
  split; first exact (proj1 Hboundary).
  split; first exact (proj1 (proj2 Hboundary)).
  split; first exact (proj2 (proj2 Hboundary)).
  split; first (rewrite Hx2'; exact Hx2).
  split.
  { rewrite writeSuccess156e4AfterRegs.
    rewrite writeSuccess156e4RegsLookupOther; last discriminate.
    rewrite writeSuccess156e0RegsLookupOther; [|discriminate|discriminate].
    unfold writeSuccess156dcRegs. rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert. reflexivity. }
  split.
  { rewrite writeSuccess156e4AfterRegs.
    rewrite writeSuccess156e4RegsLookupOther; last discriminate.
    unfold writeSuccess156e0Regs. rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert. rewrite writeSuccessWithdrawalsCounterDecrementS.
    reflexivity. }
  split; first (rewrite Hx18'; exact Hx18).
  split.
  { apply writeSuccessWithdrawalsTailRegisterFacts with
      (global := (writeSuccessWithdrawalsIteration410Endpoint finalRegs
        finalGlobal sp withdrawal).2). exact Hfacts. }
  split.
  { apply writeSuccessWithdrawalsTailRegisterFrame with
      (global := (writeSuccessWithdrawalsIteration410Endpoint finalRegs
        finalGlobal sp withdrawal).2). exact Hframe. }
  split.
  { unfold writeSuccess156e4After. destruct decide; exact Htable. }
  unfold writeSuccess156e4After. destruct decide; reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsFinalEncoderTailStatePackage.
