From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIteration.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsConcreteEntry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsCallEntry.

Import ListNotations.

Lemma writeSuccessWithdrawalsConcreteEntryRunSix machine view sp base total
    processed remaining bytes prefix suffix scratch :
  writeSuccessWithdrawalsConcreteEntry machine view sp base total processed
    remaining bytes prefix suffix scratch ->
  exists segments,
    IslaInstructionRun 6 machine segments
      ((writeSuccessInstructionAt IslaTraces.write_success_02.a101d8.a101d8
          (writeSuccessWithdrawalsMemcpyFirstResultRegs
            (match machine with
             | (local, _) => local.(seq_regs)
             end) sp
            (Z_to_bv 64 (writeSuccessIterationPointer view)))),
       machine.2).
Proof.
  intros Hentry.
  destruct Hentry as
    (regs & global & Hmachine & Htable & Hpc & Hsp & Hx10 & Hpointer &
     Hcount & Hx18 & Hmstatus & Harchitecture & Hregisters & Hrest).
  subst machine. destruct Hx10 as [oldX10 Hx10].
  destruct (Hregisters "x12") as [x12 Hx12]; first (cbn; tauto).
  destruct (Hregisters "x11") as [x11 Hx11]; first (cbn; tauto).
  destruct (Hregisters "x1") as [x1 Hx1]; first (cbn; tauto).
  destruct (Hregisters "x15") as [x15 Hx15]; first (cbn; tauto).
  destruct (writeSuccessWithdrawalsFirstInstructionSegment regs global sp
    oldX10 Htable Hpc Hsp Hx10 Hmstatus) as [first Hfirst].
  destruct (writeSuccessWithdrawalsSecondInstructionSegment regs global sp
    (RVal_Bits x12) Htable Hx12 Hmstatus) as [second Hsecond].
  destruct (writeSuccessWithdrawalsThirdInstructionSegment regs global sp
    (Z_to_bv 64 (writeSuccessIterationPointer view)) (RVal_Bits x11)
    Htable Hpointer Hx11 Hmstatus) as [third Hthird].
  destruct (writeSuccessWithdrawalsFourthInstructionSegment regs global sp
    (Z_to_bv 64 (writeSuccessIterationPointer view)) (RVal_Bits x1)
    Htable Hx1 Hmstatus) as [fourth Hfourth].
  destruct (writeSuccessWithdrawalsCallInstructionSegment regs global sp
    (Z_to_bv 64 (writeSuccessIterationPointer view)) Htable Hmstatus)
    as [call Hcall].
  destruct (writeSuccessWithdrawalsMemcpyFirstInstructionSegment regs global sp
    (Z_to_bv 64 (writeSuccessIterationPointer view)) (RVal_Bits x15)
    Htable Hx15 Hmstatus) as [memcpyFirst HmemcpyFirst].
  exists [first; second; third; fourth; call; memcpyFirst].
  econstructor; first exact Hfirst.
  econstructor; first exact Hsecond.
  econstructor; first exact Hthird.
  econstructor; first exact Hfourth.
  econstructor; first exact Hcall.
  econstructor; first exact HmemcpyFirst.
  constructor.
Qed.

Print Assumptions writeSuccessWithdrawalsConcreteEntryRunSix.
