From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a15698.
Require Import IslaTraces.write_success_90.a1569c.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess15698Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a15698).
Definition writeSuccess15698Trace2 := writeSuccessTraceTail writeSuccess15698Trace1.
Definition writeSuccess15698Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15698)) 3
    (writeSuccessTraceTail writeSuccess15698Trace2).
Definition writeSuccess15698Trace4 := writeSuccessTraceTail writeSuccess15698Trace3.
Definition writeSuccess15698NextPc : bv 64 :=
  (Z_to_bv 64 0x15698 + BV 64 4)%bv.
Definition writeSuccess15698Trace5 :=
  subst_trace (Val_Bits writeSuccess15698NextPc) 4
    (writeSuccessTraceTail writeSuccess15698Trace4).
Definition writeSuccess15698Trace6 := writeSuccessTraceTail writeSuccess15698Trace5.
Definition writeSuccess15698Trace7 := writeSuccessTraceTail writeSuccess15698Trace6.

Definition writeSuccess15698Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess15698NextPc]>
    (<["x12" := RVal_Bits (BV 64 48)]> regs).

Lemma writeSuccess15698RegsLookupOther regs reg :
  reg <> "PC" ->
  reg <> "x12" ->
  writeSuccess15698Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx12. unfold writeSuccess15698Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Lemma writeSuccess15698RegsDom regs oldX12 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15698)) ->
  regs !! "x12" = Some oldX12 ->
  dom (writeSuccess15698Regs regs) = dom regs.
Proof.
  intros Hpc Hx12.
  apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx12.
  unfold writeSuccess15698Regs. rewrite !dom_insert_L.
  set_solver.
Qed.

Definition writeSuccess15698Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a15698 regs, global).

Definition writeSuccess15698After (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a1569c (writeSuccess15698Regs regs), global).

Lemma writeSuccess15698NextPcExact :
  writeSuccess15698NextPc = Z_to_bv 64 0x1569c.
Proof. unfold writeSuccess15698NextPc. bv_solve. Qed.

Definition writeSuccess15698PrefixObservations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15698Trace1 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15698Trace2 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15698Trace3 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15698Trace4 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15698Trace5 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15698Trace6
       (<["x12" := RVal_Bits (BV 64 48)]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15698Trace7
       (writeSuccess15698Regs regs)) global].

Definition writeSuccess15698Observations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  writeSuccess15698PrefixObservations regs global ++
  [writeSuccess15694Observation
     (writeSuccess15698After regs global).1 global].

Lemma segment_15698_mstatus (regs : reg_map) (global : seq_global_state) oldX12 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15698)) ->
  regs !! "x12" = Some oldX12 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15698 = Some a15698 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15698Before regs global)
    (writeSuccess15698Observations regs global)
    (writeSuccess15698After regs global) /\
  (writeSuccess15698After regs global).1.(seq_regs) =
    writeSuccess15698Regs regs /\
  (writeSuccess15698After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15698Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess15698Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess15698Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15698), a15698.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess15698PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15698Before, writeSuccess15698Trace1,
        writeSuccessTraceTail, a15698. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess15698Trace1, writeSuccessTraceTail, a15698. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15698Trace2, writeSuccess15698Trace1,
        writeSuccessTraceTail, a15698. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15698). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x15698))
        (value := RVal_Bits (Z_to_bv 64 0x15698)).
      - reflexivity.
      - unfold writeSuccess15698Trace3, writeSuccess15698Trace2,
          writeSuccess15698Trace1, writeSuccessTraceTail, a15698. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15698Trace5, writeSuccess15698Trace4,
        writeSuccess15698Trace3, writeSuccess15698Trace2,
        writeSuccess15698Trace1, writeSuccess15698NextPc,
        writeSuccessTraceTail, a15698. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x15698 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX12)
        (value := RVal_Bits (BV 64 48))
        (updated := RVal_Bits (BV 64 48)).
      - reflexivity.
      - unfold writeSuccess15698Trace5, writeSuccess15698Trace4,
          writeSuccess15698Trace3, writeSuccess15698Trace2,
          writeSuccess15698Trace1, writeSuccessTraceTail, a15698. cbn.
        constructor.
      - exact Hx12.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x15698))
        (value := RVal_Bits writeSuccess15698NextPc)
        (updated := RVal_Bits writeSuccess15698NextPc).
      - reflexivity.
      - unfold writeSuccess15698Trace6, writeSuccess15698Trace5,
          writeSuccess15698Trace4, writeSuccess15698Trace3,
          writeSuccess15698Trace2, writeSuccess15698Trace1,
          writeSuccessTraceTail, a15698. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a1569c) (trace := a1569c).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x1569c).
      unfold writeSuccess15698Regs. rewrite lookup_insert.
      rewrite writeSuccess15698NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x1569c), a1569c.
    cbn. unfold writeSuccess15698Regs. rewrite lookup_insert.
    rewrite writeSuccess15698NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_15698 (regs : reg_map) (global : seq_global_state) oldX12 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15698)) ->
  regs !! "x12" = Some oldX12 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15698 = Some a15698 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15698Before regs global)
    (writeSuccess15698Observations regs global)
    (writeSuccess15698After regs global) /\
  (writeSuccess15698After regs global).1.(seq_regs) =
    writeSuccess15698Regs regs /\
  (writeSuccess15698After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15698Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  eapply segment_15698_mstatus; eauto.
Qed.

Print Assumptions segment_15698_mstatus.
Print Assumptions segment_15698.
Print Assumptions writeSuccess15698RegsLookupOther.
Print Assumptions writeSuccess15698RegsDom.
