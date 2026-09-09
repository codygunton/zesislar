From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyState.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPrefix15694InvMemcpy args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  Inv_memcpy (sp + BV 64 1744)%bv pointer (Z_to_bv 64 0x156a8) current scratch
    state.1.2.(seq_mem) priorLog
    (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog).
Proof.
  intros Hinv.
  have Htable : writeSuccessWithdrawalsInstructionTable state.1.2 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hfacts : writeSuccessWithdrawalsOperationalRegisterFacts
      state.1.1.(seq_regs) by (unfold Inv_15694 in Hinv; tauto).
  have Hcurrent : length current = 48%nat by
    (unfold Inv_15694 in Hinv; tauto).
  destruct (writeSuccessWithdrawalsPrefix15694MemcpyMemory args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (Hsource & Hdestination & Hrange & HsourceLower & HsourceUpper &
     HdestinationLower & HdestinationUpper & Hdisjoint & Hbacked & Hframe).
  destruct (writeSuccessMemcpyCaller156a8 state.1.2 Htable) as
    (HreturnAlign & HreturnLookup).
  unfold Inv_memcpy.
  split. { apply writeSuccessWithdrawalsPrefixAfterBoundary. exact Htable. }
  split. { reflexivity. }
  split.
  { unfold writeSuccessWithdrawalsConcretePc.
    change (match writeSuccessWithdrawalsPrefixRegs state.1.1.(seq_regs) sp
      pointer !! "PC" with
      | Some (RVal_Bits value) => Some (bvn_unsigned value)
      | _ => None
      end = Some 0x101d4).
    rewrite writeSuccessWithdrawalsPrefixRegsPc. reflexivity. }
  split.
  { change (writeSuccessWithdrawalsPrefixRegs state.1.1.(seq_regs) sp pointer !!
      "x1" = Some (RVal_Bits (Z_to_bv 64 0x156a8))).
    apply writeSuccessWithdrawalsPrefixRegsX1. }
  split.
  { change (writeSuccessWithdrawalsPrefixRegs state.1.1.(seq_regs) sp pointer !!
      "x10" = Some (RVal_Bits (sp + BV 64 1744)%bv)).
    apply writeSuccessWithdrawalsPrefixRegsX10. }
  split.
  { change (writeSuccessWithdrawalsPrefixRegs state.1.1.(seq_regs) sp pointer !!
      "x11" = Some (RVal_Bits pointer)).
    apply writeSuccessWithdrawalsPrefixRegsX11. }
  split.
  { rewrite Hcurrent.
    replace (Z_to_bv 64 (Z.of_nat 48)) with (BV 64 48) by
      (apply bv_eq; native_compute; reflexivity).
    change (writeSuccessWithdrawalsPrefixRegs state.1.1.(seq_regs) sp pointer !!
      "x12" = Some (RVal_Bits (BV 64 48))).
    apply writeSuccessWithdrawalsPrefixRegsX12. }
  split. { exact HreturnAlign. }
  split. { exact HreturnLookup. }
  split. { exact Htable. }
  split.
  { change (writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessWithdrawalsPrefixRegs state.1.1.(seq_regs) sp pointer)).
    apply writeSuccessWithdrawalsPrefixRegsOperationalFacts. exact Hfacts. }
  split. { exact Hsource. }
  split. { exact Hdestination. }
  split. { exact Hrange. }
  split. { exact HsourceLower. }
  split. { exact HsourceUpper. }
  split. { exact HdestinationLower. }
  split. { exact HdestinationUpper. }
  split. { exact Hdisjoint. }
  split. { exact Hbacked. }
  split. { exact Hframe. }
  reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefix15694InvMemcpy.
