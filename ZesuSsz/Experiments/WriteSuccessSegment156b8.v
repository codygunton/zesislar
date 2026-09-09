From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_92.a156b8.
Require Import IslaTraces.write_success_92.a156bc.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156b8Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156b8).
Definition writeSuccess156b8Trace2 := writeSuccessTraceTail writeSuccess156b8Trace1.
Definition writeSuccess156b8Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156b8)) 3
    (writeSuccessTraceTail writeSuccess156b8Trace2).
Definition writeSuccess156b8Trace4 := writeSuccessTraceTail writeSuccess156b8Trace3.
Definition writeSuccess156b8NextPc : bv 64 :=
  (Z_to_bv 64 0x156b8 + BV 64 4)%bv.
Definition writeSuccess156b8Trace5 :=
  subst_trace (Val_Bits writeSuccess156b8NextPc) 4
    (writeSuccessTraceTail writeSuccess156b8Trace4).
Definition writeSuccess156b8Link : bv 64 :=
  (Z_to_bv 64 0x156b8 + BV 64 0x0)%bv.
Definition writeSuccess156b8Trace6 :=
  subst_trace (Val_Bits writeSuccess156b8Link) 5
    (writeSuccessTraceTail writeSuccess156b8Trace5).
Definition writeSuccess156b8Trace7 := writeSuccessTraceTail writeSuccess156b8Trace6.
Definition writeSuccess156b8Trace8 := writeSuccessTraceTail writeSuccess156b8Trace7.

Definition writeSuccess156b8Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156b8NextPc]>
    (<["x1" := RVal_Bits writeSuccess156b8Link]> regs).

Lemma writeSuccess156b8RegsLookupOther regs reg :
  reg <> "PC" ->
  reg <> "x1" ->
  writeSuccess156b8Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx12. unfold writeSuccess156b8Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Lemma writeSuccess156b8RegsDom regs oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b8)) ->
  regs !! "x1" = Some oldX1 ->
  dom (writeSuccess156b8Regs regs) = dom regs.
Proof.
  intros Hpc Hx12.
  apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx12.
  unfold writeSuccess156b8Regs. rewrite !dom_insert_L.
  set_solver.
Qed.

Definition writeSuccess156b8Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156b8 regs, global).

Definition writeSuccess156b8After (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156bc (writeSuccess156b8Regs regs), global).

Lemma writeSuccess156b8NextPcExact :
  writeSuccess156b8NextPc = Z_to_bv 64 0x156bc.
Proof. unfold writeSuccess156b8NextPc. bv_solve. Qed.

Definition writeSuccess156b8PrefixObservations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b8Trace1 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b8Trace2 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b8Trace3 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b8Trace4 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b8Trace5 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b8Trace6 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b8Trace7
       (<["x1" := RVal_Bits writeSuccess156b8Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b8Trace8
       (writeSuccess156b8Regs regs)) global].

Definition writeSuccess156b8Observations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  writeSuccess156b8PrefixObservations regs global ++
  [writeSuccess15694Observation
     (writeSuccess156b8After regs global).1 global].

Lemma segment_156b8_mstatus (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b8)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b8 = Some a156b8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156bc = Some a156bc ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156b8Before regs global)
    (writeSuccess156b8Observations regs global)
    (writeSuccess156b8After regs global) /\
  (writeSuccess156b8After regs global).1.(seq_regs) =
    writeSuccess156b8Regs regs /\
  (writeSuccess156b8After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156b8Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156b8Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156b8Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156b8), a156b8.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156b8PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156b8Before, writeSuccess156b8Trace1,
        writeSuccessTraceTail, a156b8. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess156b8Trace1, writeSuccessTraceTail, a156b8. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156b8Trace2, writeSuccess156b8Trace1,
        writeSuccessTraceTail, a156b8. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156b8). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x156b8))
        (value := RVal_Bits (Z_to_bv 64 0x156b8)).
      - reflexivity.
      - unfold writeSuccess156b8Trace3, writeSuccess156b8Trace2,
          writeSuccess156b8Trace1, writeSuccessTraceTail, a156b8. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156b8Trace5, writeSuccess156b8Trace4,
        writeSuccess156b8Trace3, writeSuccess156b8Trace2,
        writeSuccess156b8Trace1, writeSuccess156b8NextPc,
        writeSuccessTraceTail, a156b8. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x156b8 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156b8Trace5, writeSuccess156b8Trace4,
        writeSuccess156b8Trace3, writeSuccess156b8Trace2,
        writeSuccess156b8Trace1, writeSuccess156b8Link,
        writeSuccessTraceTail, a156b8. cbn.
      eapply DefineConstS with
        (v := Val_Bits
          (Z_to_bv 64 0x156b8 + BV 64 0x0)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX1)
        (value := RVal_Bits writeSuccess156b8Link)
        (updated := RVal_Bits writeSuccess156b8Link).
      - reflexivity.
      - unfold writeSuccess156b8Trace6, writeSuccess156b8Trace5,
          writeSuccess156b8Link, writeSuccess156b8Trace4,
          writeSuccess156b8Trace3, writeSuccess156b8Trace2,
          writeSuccess156b8Trace1, writeSuccessTraceTail, a156b8. cbn.
        constructor.
      - exact Hx12.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x156b8))
        (value := RVal_Bits writeSuccess156b8NextPc)
        (updated := RVal_Bits writeSuccess156b8NextPc).
      - reflexivity.
      - unfold writeSuccess156b8Trace7, writeSuccess156b8Trace6,
          writeSuccess156b8Trace5,
          writeSuccess156b8Trace4, writeSuccess156b8Trace3,
          writeSuccess156b8Trace2, writeSuccess156b8Trace1,
          writeSuccessTraceTail, a156b8. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156bc) (trace := a156bc).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x156bc).
      unfold writeSuccess156b8Regs. rewrite lookup_insert.
      rewrite writeSuccess156b8NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156bc), a156bc.
    cbn. unfold writeSuccess156b8Regs. rewrite lookup_insert.
    rewrite writeSuccess156b8NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_156b8 (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b8)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b8 = Some a156b8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156bc = Some a156bc ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156b8Before regs global)
    (writeSuccess156b8Observations regs global)
    (writeSuccess156b8After regs global) /\
  (writeSuccess156b8After regs global).1.(seq_regs) =
    writeSuccess156b8Regs regs /\
  (writeSuccess156b8After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156b8Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  eapply segment_156b8_mstatus; eauto.
Qed.

Print Assumptions segment_156b8_mstatus.
Print Assumptions segment_156b8.
Print Assumptions writeSuccess156b8RegsLookupOther.
Print Assumptions writeSuccess156b8RegsDom.
