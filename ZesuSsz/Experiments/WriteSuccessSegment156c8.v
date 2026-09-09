From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_93.a156c8.
Require Import IslaTraces.write_success_93.a156cc.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156c8Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156c8).
Definition writeSuccess156c8Trace2 := writeSuccessTraceTail writeSuccess156c8Trace1.
Definition writeSuccess156c8Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156c8)) 3
    (writeSuccessTraceTail writeSuccess156c8Trace2).
Definition writeSuccess156c8Trace4 := writeSuccessTraceTail writeSuccess156c8Trace3.
Definition writeSuccess156c8NextPc : bv 64 :=
  (Z_to_bv 64 0x156c8 + BV 64 4)%bv.
Definition writeSuccess156c8Trace5 :=
  subst_trace (Val_Bits writeSuccess156c8NextPc) 4
    (writeSuccessTraceTail writeSuccess156c8Trace4).
Definition writeSuccess156c8Link : bv 64 :=
  (Z_to_bv 64 0x156c8 + BV 64 0xffffffffffffb000)%bv.
Definition writeSuccess156c8Trace6 :=
  subst_trace (Val_Bits writeSuccess156c8Link) 5
    (writeSuccessTraceTail writeSuccess156c8Trace5).
Definition writeSuccess156c8Trace7 := writeSuccessTraceTail writeSuccess156c8Trace6.
Definition writeSuccess156c8Trace8 := writeSuccessTraceTail writeSuccess156c8Trace7.

Definition writeSuccess156c8Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156c8NextPc]>
    (<["x1" := RVal_Bits writeSuccess156c8Link]> regs).

Lemma writeSuccess156c8RegsLookupOther regs reg :
  reg <> "PC" ->
  reg <> "x1" ->
  writeSuccess156c8Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx12. unfold writeSuccess156c8Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Lemma writeSuccess156c8RegsDom regs oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c8)) ->
  regs !! "x1" = Some oldX1 ->
  dom (writeSuccess156c8Regs regs) = dom regs.
Proof.
  intros Hpc Hx12.
  apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx12.
  unfold writeSuccess156c8Regs. rewrite !dom_insert_L.
  set_solver.
Qed.

Definition writeSuccess156c8Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156c8 regs, global).

Definition writeSuccess156c8After (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156cc (writeSuccess156c8Regs regs), global).

Lemma writeSuccess156c8NextPcExact :
  writeSuccess156c8NextPc = Z_to_bv 64 0x156cc.
Proof. unfold writeSuccess156c8NextPc. bv_solve. Qed.

Definition writeSuccess156c8PrefixObservations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c8Trace1 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c8Trace2 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c8Trace3 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c8Trace4 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c8Trace5 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c8Trace6 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c8Trace7
       (<["x1" := RVal_Bits writeSuccess156c8Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c8Trace8
       (writeSuccess156c8Regs regs)) global].

Definition writeSuccess156c8Observations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  writeSuccess156c8PrefixObservations regs global ++
  [writeSuccess15694Observation
     (writeSuccess156c8After regs global).1 global].

Lemma segment_156c8_mstatus (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c8)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c8 = Some a156c8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156cc = Some a156cc ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156c8Before regs global)
    (writeSuccess156c8Observations regs global)
    (writeSuccess156c8After regs global) /\
  (writeSuccess156c8After regs global).1.(seq_regs) =
    writeSuccess156c8Regs regs /\
  (writeSuccess156c8After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156c8Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156c8Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156c8Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156c8), a156c8.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156c8PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156c8Before, writeSuccess156c8Trace1,
        writeSuccessTraceTail, a156c8. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess156c8Trace1, writeSuccessTraceTail, a156c8. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156c8Trace2, writeSuccess156c8Trace1,
        writeSuccessTraceTail, a156c8. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156c8). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x156c8))
        (value := RVal_Bits (Z_to_bv 64 0x156c8)).
      - reflexivity.
      - unfold writeSuccess156c8Trace3, writeSuccess156c8Trace2,
          writeSuccess156c8Trace1, writeSuccessTraceTail, a156c8. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156c8Trace5, writeSuccess156c8Trace4,
        writeSuccess156c8Trace3, writeSuccess156c8Trace2,
        writeSuccess156c8Trace1, writeSuccess156c8NextPc,
        writeSuccessTraceTail, a156c8. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x156c8 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156c8Trace5, writeSuccess156c8Trace4,
        writeSuccess156c8Trace3, writeSuccess156c8Trace2,
        writeSuccess156c8Trace1, writeSuccess156c8Link,
        writeSuccessTraceTail, a156c8. cbn.
      eapply DefineConstS with
        (v := Val_Bits
          (Z_to_bv 64 0x156c8 + BV 64 0xffffffffffffb000)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX1)
        (value := RVal_Bits writeSuccess156c8Link)
        (updated := RVal_Bits writeSuccess156c8Link).
      - reflexivity.
      - unfold writeSuccess156c8Trace6, writeSuccess156c8Trace5,
          writeSuccess156c8Link, writeSuccess156c8Trace4,
          writeSuccess156c8Trace3, writeSuccess156c8Trace2,
          writeSuccess156c8Trace1, writeSuccessTraceTail, a156c8. cbn.
        constructor.
      - exact Hx12.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x156c8))
        (value := RVal_Bits writeSuccess156c8NextPc)
        (updated := RVal_Bits writeSuccess156c8NextPc).
      - reflexivity.
      - unfold writeSuccess156c8Trace7, writeSuccess156c8Trace6,
          writeSuccess156c8Trace5,
          writeSuccess156c8Trace4, writeSuccess156c8Trace3,
          writeSuccess156c8Trace2, writeSuccess156c8Trace1,
          writeSuccessTraceTail, a156c8. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156cc) (trace := a156cc).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x156cc).
      unfold writeSuccess156c8Regs. rewrite lookup_insert.
      rewrite writeSuccess156c8NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156cc), a156cc.
    cbn. unfold writeSuccess156c8Regs. rewrite lookup_insert.
    rewrite writeSuccess156c8NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_156c8 (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c8)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c8 = Some a156c8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156cc = Some a156cc ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156c8Before regs global)
    (writeSuccess156c8Observations regs global)
    (writeSuccess156c8After regs global) /\
  (writeSuccess156c8After regs global).1.(seq_regs) =
    writeSuccess156c8Regs regs /\
  (writeSuccess156c8After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156c8Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  eapply segment_156c8_mstatus; eauto.
Qed.

Print Assumptions segment_156c8_mstatus.
Print Assumptions segment_156c8.
Print Assumptions writeSuccess156c8RegsLookupOther.
Print Assumptions writeSuccess156c8RegsDom.
