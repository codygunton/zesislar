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

Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsTailStatePackage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsTailMemoryPackage.

Lemma writeSuccessWithdrawalsFinalEncoderTailEndpointPackage args sp pointer base
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
  writeSuccessWithdrawalsMemoryFrame sp after.2.(seq_mem) memoryFrame /\
  read_mem_list after.2.(seq_mem)
    (bv_unsigned (sp + BV 64 1744)%bv) 48%N = Some current /\
  read_mem_list after.2.(seq_mem) (bv_unsigned sp - 16) 16%N =
    Some
      (bv_to_little_endian 8 8
         (bv_unsigned (writeSuccessWithdrawalsAmountValue withdrawal)) ++
       bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 0x156dc))) /\
  set_Forall
    (fun address =>
      ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom after.2.(seq_mem)) /\
  writeSuccessWithdrawalsInstructionTable after.2 /\
  after.2 = endpoint.2.
Proof.
  intros Hinv Hp He1 He2 Ho Hfinal. cbn.
  destruct (writeSuccessWithdrawalsFinalEncoderTailStatePackage args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal
    Hinv Hp He1 He2 Ho Hfinal) as
    (Hboundary & HpcReg & Hpc & Hx2 & Hx8 & Hx9 & Hx18 & Hfacts & HregsFrame &
      Htable & Hglobal).
  destruct (writeSuccessWithdrawalsFinalEncoderTailMemoryPackage args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal
    Hinv Hp He1 He2 Ho Hfinal) as
    (HmemoryFrame & Hhigh & Hscratch & Hmmio & Hglobal').
  split; first exact Hboundary.
  split; first exact HpcReg.
  split; first exact Hpc.
  split; first exact Hx2.
  split; first exact Hx8.
  split; first exact Hx9.
  split; first exact Hx18.
  split; first exact Hfacts.
  split; first exact HregsFrame.
  split; first exact HmemoryFrame.
  split; first exact Hhigh.
  split; first exact Hscratch.
  split; first exact Hmmio.
  split; first exact Htable.
  exact Hglobal.
Qed.

Print Assumptions writeSuccessWithdrawalsFinalEncoderTailEndpointPackage.
