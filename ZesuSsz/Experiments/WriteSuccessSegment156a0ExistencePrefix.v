Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a156a0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0Defs.

Lemma segment_156a0_prefix_exists regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a0)) ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionPrefixPath (writeSuccess156a0Before regs global)
    (writeSuccess156a0First5Observations regs global)
    (writeSuccess15694Local writeSuccess156a0Trace5 regs, global).
Proof.
  intros Hpc Hmstatus.
  unfold writeSuccess156a0First5Observations,
    writeSuccess156a0PrefixObservations. cbn.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess156a0Before, writeSuccess156a0Trace1,
      writeSuccessTraceTail, a156a0. cbn.
    apply DeclareConstBitVecS' with (b := BV 64 0). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssume; first reflexivity.
    unfold writeSuccess156a0Trace1, writeSuccessTraceTail, a156a0. cbn.
    eapply AssumeS. exact Hmstatus. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess156a0Trace2, writeSuccess156a0Trace1,
      writeSuccessTraceTail, a156a0. cbn.
    apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156a0). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with
      (root := RVal_Bits (Z_to_bv 64 0x156a0))
      (value := RVal_Bits (Z_to_bv 64 0x156a0)).
    - reflexivity.
    - unfold writeSuccess156a0Trace3, writeSuccess156a0Trace2,
        writeSuccess156a0Trace1, writeSuccessTraceTail, a156a0. cbn.
      constructor.
    - exact Hpc.
    - reflexivity.
    - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess156a0Trace5, writeSuccess156a0Trace4,
      writeSuccess156a0Trace3, writeSuccess156a0Trace2,
      writeSuccess156a0Trace1, writeSuccess156a0NextPc,
      writeSuccessTraceTail, a156a0. cbn.
    eapply DefineConstS with
      (v := Val_Bits (Z_to_bv 64 0x156a0 + BV 64 4)%bv).
    reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Print Assumptions segment_156a0_prefix_exists.
