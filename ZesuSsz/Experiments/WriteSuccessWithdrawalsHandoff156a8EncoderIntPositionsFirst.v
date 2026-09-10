From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156a8.
Require Import IslaTraces.write_success_91.a156ac.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.

Lemma writeSuccessWithdrawals156a8PositionsFirst regs global (sp pointer : bv 64)
    current withdrawal (mstatusBits satp oldDest : bv 64) segments after :
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x156a8)) ->
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "x2" = Some (RVal_Bits sp) ->
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "mstatus" =
    Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "satp" = Some (RVal_Bits satp) ->
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "x10" = Some (RVal_Bits oldDest) ->
  writeSuccess156a8SysRegs (writeSuccessWithdrawals156a8Regs regs global sp pointer current) ->
  eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current) writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current) writeSuccess156a8Aligned = Some (Val_Bool true) ->
  eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current) writeSuccess156a8Lower = Some (Val_Bool true) ->
  eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current) writeSuccess156a8Upper = Some (Val_Bool true) ->
  read_mem (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_mem)
    (bv_unsigned (writeSuccess156a8Address sp)) 8 = Some (bv_to_bvn (writeSuccessWithdrawalsIndexValue withdrawal)) ->
  (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs) !! Z_to_bv 64 0x156a8 = Some a156a8 ->
  (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  IslaInstructionRun 3 (writeSuccessWithdrawals156a8State regs global sp pointer current) segments after ->
  exists observations tail,
    segments = observations :: tail /\
    observations = writeSuccess156a8Observations
      (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
      (writeSuccessWithdrawals156a8Global regs global sp pointer current)
      mstatusBits sp satp (writeSuccessWithdrawalsIndexValue withdrawal) /\
    IslaInstructionRun 2 (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal) tail after /\
    IslaInstructionSegment (writeSuccessWithdrawals156a8State regs global sp pointer current)
      observations (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal).
Proof.
  intros Hpc Hsp Hmstatus Hsatp Hdest Hsys Hma Ha Hl Hu Hread Hcode Hnext Hrun.
  inversion Hrun as [|? ? obs middle tail machineAfter Hseg Htail]; subst.
  destruct (segment_156a8_covered _ _ mstatusBits sp satp
    (writeSuccessWithdrawalsIndexValue withdrawal) oldDest obs middle Hpc Hsp
    Hmstatus Hsatp Hdest Hsys Hma Ha Hl Hu Hread Hcode Hnext Hseg) as (-> & ->).
  exists (writeSuccess156a8Observations
    (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
    (writeSuccessWithdrawals156a8Global regs global sp pointer current)
    mstatusBits sp satp (writeSuccessWithdrawalsIndexValue withdrawal)), tail.
  repeat split; assumption || reflexivity.
Qed.
Print Assumptions writeSuccessWithdrawals156a8PositionsFirst.
