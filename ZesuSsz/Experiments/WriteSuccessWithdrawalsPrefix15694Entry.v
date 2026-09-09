From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a15694.
Require Import IslaTraces.write_success_90.a15698.
Require Import IslaTraces.write_success_90.a1569c.
Require Import IslaTraces.write_success_90.a156a0.
Require Import IslaTraces.write_success_90.a156a4.
Require Import IslaTraces.write_success_02.a101d4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessWithdrawalsSilentSegmentRecords before observations :
  concat (map microLabels observations) = [] ->
  segmentRecords before observations = [].
Proof.
  revert before. induction observations as [|observation observations IH];
    intros before Hlabels; first reflexivity.
  cbn in Hlabels. apply app_eq_nil in Hlabels as [Hhead Htail].
  unfold segmentRecords. cbn. rewrite Hhead. cbn.
  apply IH. exact Htail.
Qed.

Lemma writeSuccessWithdrawalsSilentRecordedSnoc count before segments middle
    observations machineAfter :
  WriteSuccessWithdrawalsRecordedRun count before segments middle ->
  IslaInstructionSegment middle.1 observations machineAfter ->
  concat (map microLabels observations) = [] ->
  WriteSuccessWithdrawalsRecordedRun (S count) before (segments ++ [observations])
    (machineAfter, middle.2).
Proof.
  intros Hrun Hsegment Hlabels.
  pose proof (writeSuccessWithdrawalsRecordedRunSnoc count before segments middle
    observations machineAfter Hrun Hsegment) as Hsnoc.
  rewrite (writeSuccessWithdrawalsSilentSegmentRecords middle.1 observations
    Hlabels) in Hsnoc. rewrite app_nil_r in Hsnoc. exact Hsnoc.
Qed.

Definition writeSuccessWithdrawalsPrefixState98 (state : IslaState) (sp : bv 64) : IslaState :=
  writeSuccess15694After state.1.(seq_regs) state.2 sp.

Definition writeSuccessWithdrawalsPrefixState9c (state : IslaState) (sp : bv 64) : IslaState :=
  writeSuccess15698After
    (writeSuccessWithdrawalsPrefixState98 state sp).1.(seq_regs)
    (writeSuccessWithdrawalsPrefixState98 state sp).2.

Definition writeSuccessWithdrawalsPrefixStatea0 (state : IslaState)
    (sp pointer : bv 64) : IslaState :=
  writeSuccess1569cAfter
    (writeSuccessWithdrawalsPrefixState9c state sp).1.(seq_regs)
    (writeSuccessWithdrawalsPrefixState9c state sp).2 pointer.

Definition writeSuccessWithdrawalsPrefixStatea4 (state : IslaState)
    (sp pointer : bv 64) : IslaState :=
  writeSuccess156a0After
    (writeSuccessWithdrawalsPrefixStatea0 state sp pointer).1.(seq_regs)
    (writeSuccessWithdrawalsPrefixStatea0 state sp pointer).2.

Definition writeSuccessWithdrawalsPrefixAfter (state : IslaState)
    (sp pointer : bv 64) : IslaState :=
  writeSuccess156a4After
    (writeSuccessWithdrawalsPrefixStatea4 state sp pointer).1.(seq_regs)
    (writeSuccessWithdrawalsPrefixStatea4 state sp pointer).2.

Lemma writeSuccessWithdrawalsInv15694DirectEntry args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  exists oldX1 oldX10 oldX11 oldX12,
    state.1 = writeSuccess15694Before state.1.1.(seq_regs) state.1.2 /\
    state.1.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15694)) /\
    state.1.1.(seq_regs) !! "x1" = Some oldX1 /\
    state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) /\
    state.1.1.(seq_regs) !! "x8" = Some (RVal_Bits pointer) /\
    state.1.1.(seq_regs) !! "x10" = Some oldX10 /\
    state.1.1.(seq_regs) !! "x11" = Some oldX11 /\
    state.1.1.(seq_regs) !! "x12" = Some oldX12 /\
    writeSuccessWithdrawalsInstructionTable state.1.2 /\
    eval_a_exp state.1.1.(seq_regs) writeSuccess15694Mstatus =
      Some (Val_Bool true).
Proof.
  intros Hinv.
  have Hboundary : IslaInstructionBoundary state.1 by
    (unfold Inv_15694 in Hinv; tauto).
  have HpcReg : state.1.1.(seq_pc_reg) = "PC" by
    (unfold Inv_15694 in Hinv; tauto).
  have Hpc : writeSuccessWithdrawalsConcretePc state = Some 0x15694 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hx1 : exists oldX1, state.1.1.(seq_regs) !! "x1" = Some oldX1 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hx10 : exists oldX10, state.1.1.(seq_regs) !! "x10" = Some oldX10 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hx11 : exists oldX11, state.1.1.(seq_regs) !! "x11" = Some oldX11 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hx12 : exists oldX12, state.1.1.(seq_regs) !! "x12" = Some oldX12 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hsp : state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hpointer : state.1.1.(seq_regs) !! "x8" = Some (RVal_Bits pointer) by
    (unfold Inv_15694 in Hinv; tauto).
  have Htable : writeSuccessWithdrawalsInstructionTable state.1.2 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hfacts : writeSuccessWithdrawalsOperationalRegisterFacts
      state.1.1.(seq_regs) by (unfold Inv_15694 in Hinv; tauto).
  destruct state as [[[trace regs pcReg nb] global] log]. cbn in *.
  subst pcReg.
  destruct Hboundary as [Hnb (pc & instruction & HpcLookup & Hcode & Htrace)].
  cbn in Hnb, Htrace.
  have HpcUnsigned : bv_unsigned pc = 0x15694.
  { unfold writeSuccessWithdrawalsConcretePc in Hpc. cbn in Hpc.
    rewrite HpcLookup in Hpc. inversion Hpc. reflexivity. }
  have HpcBits : pc = Z_to_bv 64 0x15694.
  { apply bv_eq. rewrite Z_to_bv_unsigned. cbn. exact HpcUnsigned. }
  have HpcExact : regs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15694)).
  { rewrite HpcBits in HpcLookup. exact HpcLookup. }
  have Hcode15694 : global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  rewrite HpcBits Hcode15694 in Hcode. inversion Hcode. subst instruction.
  have Hentry :
      ({| seq_trace := trace; seq_regs := regs; seq_pc_reg := "PC";
          seq_nb_state := nb |}, global) = writeSuccess15694Before regs global.
  { unfold writeSuccess15694Before, writeSuccess15694Local.
    rewrite Hnb. rewrite <- H0. reflexivity. }
  destruct Hx1 as [oldX1 Hx1]. destruct Hx10 as [oldX10 Hx10].
  destruct Hx11 as [oldX11 Hx11]. destruct Hx12 as [oldX12 Hx12].
  exists oldX1, oldX10, oldX11, oldX12. repeat split; try assumption.
  exact (proj1 Hfacts).
Qed.

Print Assumptions writeSuccessWithdrawalsSilentSegmentRecords.
Print Assumptions writeSuccessWithdrawalsSilentRecordedSnoc.
Print Assumptions writeSuccessWithdrawalsInv15694DirectEntry.
