From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d24.
Require Import IslaTraces.write_success_07.a15d28.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess15d24Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a15d24).
Definition writeSuccess15d24Trace2 := writeSuccessTraceTail writeSuccess15d24Trace1.
Definition writeSuccess15d24Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15d24)) 3
    (writeSuccessTraceTail writeSuccess15d24Trace2).
Definition writeSuccess15d24Trace4 := writeSuccessTraceTail writeSuccess15d24Trace3.
Definition writeSuccess15d24NextPc : bv 64 :=
  (Z_to_bv 64 0x15d24 + BV 64 4)%bv.
Definition writeSuccess15d24Trace5 :=
  subst_trace (Val_Bits writeSuccess15d24NextPc) 4
    (writeSuccessTraceTail writeSuccess15d24Trace4).
Definition writeSuccess15d24Link : bv 64 :=
  (Z_to_bv 64 0x15d24 + BV 64 0xffffffffffffa000)%bv.
Definition writeSuccess15d24Trace6 :=
  subst_trace (Val_Bits writeSuccess15d24Link) 5
    (writeSuccessTraceTail writeSuccess15d24Trace5).
Definition writeSuccess15d24Trace7 := writeSuccessTraceTail writeSuccess15d24Trace6.
Definition writeSuccess15d24Trace8 := writeSuccessTraceTail writeSuccess15d24Trace7.

Definition writeSuccess15d24Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess15d24NextPc]>
    (<["x1" := RVal_Bits writeSuccess15d24Link]> regs).

Lemma writeSuccess15d24RegsLookupOther regs reg :
  reg <> "PC" ->
  reg <> "x1" ->
  writeSuccess15d24Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx12. unfold writeSuccess15d24Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Lemma writeSuccess15d24RegsDom regs oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d24)) ->
  regs !! "x1" = Some oldX1 ->
  dom (writeSuccess15d24Regs regs) = dom regs.
Proof.
  intros Hpc Hx12.
  apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx12.
  unfold writeSuccess15d24Regs. rewrite !dom_insert_L.
  set_solver.
Qed.

Definition writeSuccess15d24Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a15d24 regs, global).

Definition writeSuccess15d24After (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a15d28 (writeSuccess15d24Regs regs), global).

Lemma writeSuccess15d24NextPcExact :
  writeSuccess15d24NextPc = Z_to_bv 64 0x15d28.
Proof. unfold writeSuccess15d24NextPc. bv_solve. Qed.

Definition writeSuccess15d24PrefixObservations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d24Trace1 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d24Trace2 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d24Trace3 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d24Trace4 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d24Trace5 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d24Trace6 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d24Trace7
       (<["x1" := RVal_Bits writeSuccess15d24Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d24Trace8
       (writeSuccess15d24Regs regs)) global].

Definition writeSuccess15d24Observations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  writeSuccess15d24PrefixObservations regs global ++
  [writeSuccess15694Observation
     (writeSuccess15d24After regs global).1 global].

Lemma segment_15d24_mstatus (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d24)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d28 = Some a15d28 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d24Before regs global)
    (writeSuccess15d24Observations regs global)
    (writeSuccess15d24After regs global) /\
  (writeSuccess15d24After regs global).1.(seq_regs) =
    writeSuccess15d24Regs regs /\
  (writeSuccess15d24After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15d24Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess15d24Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess15d24Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15d24), a15d24.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess15d24PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d24Before, writeSuccess15d24Trace1,
        writeSuccessTraceTail, a15d24. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess15d24Trace1, writeSuccessTraceTail, a15d24. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d24Trace2, writeSuccess15d24Trace1,
        writeSuccessTraceTail, a15d24. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15d24). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d24))
        (value := RVal_Bits (Z_to_bv 64 0x15d24)).
      - reflexivity.
      - unfold writeSuccess15d24Trace3, writeSuccess15d24Trace2,
          writeSuccess15d24Trace1, writeSuccessTraceTail, a15d24. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d24Trace5, writeSuccess15d24Trace4,
        writeSuccess15d24Trace3, writeSuccess15d24Trace2,
        writeSuccess15d24Trace1, writeSuccess15d24NextPc,
        writeSuccessTraceTail, a15d24. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x15d24 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d24Trace5, writeSuccess15d24Trace4,
        writeSuccess15d24Trace3, writeSuccess15d24Trace2,
        writeSuccess15d24Trace1, writeSuccess15d24Link,
        writeSuccessTraceTail, a15d24. cbn.
      eapply DefineConstS with
        (v := Val_Bits
          (Z_to_bv 64 0x15d24 + BV 64 0xffffffffffffa000)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX1)
        (value := RVal_Bits writeSuccess15d24Link)
        (updated := RVal_Bits writeSuccess15d24Link).
      - reflexivity.
      - unfold writeSuccess15d24Trace6, writeSuccess15d24Trace5,
          writeSuccess15d24Link, writeSuccess15d24Trace4,
          writeSuccess15d24Trace3, writeSuccess15d24Trace2,
          writeSuccess15d24Trace1, writeSuccessTraceTail, a15d24. cbn.
        constructor.
      - exact Hx12.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d24))
        (value := RVal_Bits writeSuccess15d24NextPc)
        (updated := RVal_Bits writeSuccess15d24NextPc).
      - reflexivity.
      - unfold writeSuccess15d24Trace7, writeSuccess15d24Trace6,
          writeSuccess15d24Trace5,
          writeSuccess15d24Trace4, writeSuccess15d24Trace3,
          writeSuccess15d24Trace2, writeSuccess15d24Trace1,
          writeSuccessTraceTail, a15d24. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15d28) (trace := a15d28).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x15d28).
      unfold writeSuccess15d24Regs. rewrite lookup_insert.
      rewrite writeSuccess15d24NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15d28), a15d28.
    cbn. unfold writeSuccess15d24Regs. rewrite lookup_insert.
    rewrite writeSuccess15d24NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_15d24 (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d24)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d28 = Some a15d28 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d24Before regs global)
    (writeSuccess15d24Observations regs global)
    (writeSuccess15d24After regs global) /\
  (writeSuccess15d24After regs global).1.(seq_regs) =
    writeSuccess15d24Regs regs /\
  (writeSuccess15d24After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15d24Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  eapply segment_15d24_mstatus; eauto.
Qed.

Print Assumptions segment_15d24_mstatus.
Print Assumptions segment_15d24.
Print Assumptions writeSuccess15d24RegsLookupOther.
Print Assumptions writeSuccess15d24RegsDom.
