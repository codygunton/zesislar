Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a156a0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0Defs.

Lemma segment_156a0_suffix_exists regs global oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a0)) ->
  regs !! "x1" = Some oldX1 ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local writeSuccess156a0Trace5 regs, global)
    (writeSuccess156a0TailObservations regs global)
    (writeSuccess15694Local tnil (writeSuccess156a0Regs regs), global).
Proof.
  intros Hpc Hx1.
  unfold writeSuccess156a0TailObservations,
    writeSuccess156a0PrefixObservations. cbn.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess156a0Trace5, writeSuccess156a0Trace4,
      writeSuccess156a0Trace3, writeSuccess156a0Trace2,
      writeSuccess156a0Trace1, writeSuccess156a0Link,
      writeSuccessTraceTail, a156a0. cbn.
    eapply DefineConstS with
      (v := Val_Bits
        (Z_to_bv 64 0x156a0 + BV 64 0xffffffffffffb000)%bv).
    reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqWriteReg with (root := oldX1)
      (value := RVal_Bits writeSuccess156a0Link)
      (updated := RVal_Bits writeSuccess156a0Link).
    - reflexivity.
    - unfold writeSuccess156a0Trace6, writeSuccess156a0Trace5,
        writeSuccess156a0Link, writeSuccess156a0Trace4,
        writeSuccess156a0Trace3, writeSuccess156a0Trace2,
        writeSuccess156a0Trace1, writeSuccessTraceTail, a156a0. cbn.
      constructor.
    - exact Hx1.
    - reflexivity.
    - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqWriteReg with
      (root := RVal_Bits (Z_to_bv 64 0x156a0))
      (value := RVal_Bits writeSuccess156a0NextPc)
      (updated := RVal_Bits writeSuccess156a0NextPc).
    - reflexivity.
    - unfold writeSuccess156a0Trace7, writeSuccess156a0Trace6,
        writeSuccess156a0Trace5, writeSuccess156a0Trace4,
        writeSuccess156a0Trace3, writeSuccess156a0Trace2,
        writeSuccess156a0Trace1, writeSuccessTraceTail, a156a0. cbn.
      constructor.
    - rewrite lookup_insert_ne; last done. exact Hpc.
    - reflexivity.
    - reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Print Assumptions segment_156a0_suffix_exists.
