Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalSomeBoundaries.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64SomeFrameDefinitions.

Lemma optional_u64_some_public_return
    `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8) (tail : spec)
    (r8 r9 r12 r13 r14 r15 r16 r17
     r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : bv 64) :
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret 32
      [RVal_Bits r8; RVal_Bits r9; RVal_Bits r18; RVal_Bits r19;
       RVal_Bits r20; RVal_Bits r21; RVal_Bits r22; RVal_Bits r23;
       RVal_Bits r24; RVal_Bits r25; RVal_Bits r26; RVal_Bits r27]
      ret sp
      (fun _ =>
        bv_unsigned data ↦ₘ value ∗ (bv_unsigned data + 8) ↦ₘ tag ∗
        mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True)) -∗
  instr_pre (bv_unsigned ret)
    (encoderOptionalSomeFinal data value sp ret tag r8 tail
      (optionalU64SomePublicFrame r9 r12 r13 r14 r15 r16 r17
        r18 r19 r20 r21 r22 r23 r24 r25 r26 r27)).
Proof. move => *. zesu_block. Qed.
