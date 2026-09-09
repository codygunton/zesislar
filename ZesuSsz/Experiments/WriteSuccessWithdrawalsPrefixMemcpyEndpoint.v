From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4Existence.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockMemcpyCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyAfter.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpy.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPrefixMemcpyEndpoint args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state memcpySegments after :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 339
    (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)
    memcpySegments after ->
  exists regs global returnTrace,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs global /\
    global.(seq_instrs) !! Z_to_bv 64 0x156a8 = Some returnTrace /\
    after.1 =
      (writeSuccess15694Local returnTrace
        (writeSuccessMemcpyEndpointRegs regs global pointer
          (sp + BV 64 1744)%bv current (Z_to_bv 64 0x156a8)),
       writeSuccessMemcpyEndpointGlobal regs global pointer
         (sp + BV 64 1744)%bv current).
Proof.
  intros Hinv Hrun.
  have Hcurrent : length current = 48%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have HprefixInv := writeSuccessWithdrawalsPrefix15694InvMemcpy args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
  set (middle :=
    (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)).
  change (Inv_memcpy (sp + BV 64 1744)%bv pointer (Z_to_bv 64 0x156a8)
    current scratch state.1.2.(seq_mem) priorLog middle) in HprefixInv.
  have Hrun' : WriteSuccessWithdrawalsRecordedRun (7 * length current + 3)
      middle memcpySegments after.
  { rewrite Hcurrent. exact Hrun. }
  destruct (block_memcpy_recorded_covered (sp + BV 64 1744)%bv pointer
    (Z_to_bv 64 0x156a8) current scratch state.1.2.(seq_mem) priorLog middle
    memcpySegments after HprefixInv Hrun') as
    (_ & _ & _ & _ & _ & regs & global & returnTrace & Hentry & Hreturn &
     Hafter).
  exists regs, global, returnTrace. repeat split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefixMemcpyEndpoint.
