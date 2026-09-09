From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_94.a156d4.
Require Import IslaTraces.write_success_94.a156d8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156d4Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156d4).
Definition writeSuccess156d4Trace2 := writeSuccessTraceTail writeSuccess156d4Trace1.
Definition writeSuccess156d4Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156d4)) 3
    (writeSuccessTraceTail writeSuccess156d4Trace2).
Definition writeSuccess156d4Trace4 := writeSuccessTraceTail writeSuccess156d4Trace3.
Definition writeSuccess156d4NextPc : bv 64 :=
  (Z_to_bv 64 0x156d4 + BV 64 4)%bv.
Definition writeSuccess156d4Trace5 :=
  subst_trace (Val_Bits writeSuccess156d4NextPc) 4
    (writeSuccessTraceTail writeSuccess156d4Trace4).
Definition writeSuccess156d4Link : bv 64 :=
  (Z_to_bv 64 0x156d4 + BV 64 0x0)%bv.
Definition writeSuccess156d4Trace6 :=
  subst_trace (Val_Bits writeSuccess156d4Link) 5
    (writeSuccessTraceTail writeSuccess156d4Trace5).
Definition writeSuccess156d4Trace7 := writeSuccessTraceTail writeSuccess156d4Trace6.
Definition writeSuccess156d4Trace8 := writeSuccessTraceTail writeSuccess156d4Trace7.

Definition writeSuccess156d4Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156d4NextPc]>
    (<["x1" := RVal_Bits writeSuccess156d4Link]> regs).

Lemma writeSuccess156d4RegsLookupOther regs reg :
  reg <> "PC" ->
  reg <> "x1" ->
  writeSuccess156d4Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx12. unfold writeSuccess156d4Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Lemma writeSuccess156d4RegsDom regs oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d4)) ->
  regs !! "x1" = Some oldX1 ->
  dom (writeSuccess156d4Regs regs) = dom regs.
Proof.
  intros Hpc Hx12.
  apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx12.
  unfold writeSuccess156d4Regs. rewrite !dom_insert_L.
  set_solver.
Qed.

Definition writeSuccess156d4Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156d4 regs, global).

Definition writeSuccess156d4After (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156d8 (writeSuccess156d4Regs regs), global).

Lemma writeSuccess156d4NextPcExact :
  writeSuccess156d4NextPc = Z_to_bv 64 0x156d8.
Proof. unfold writeSuccess156d4NextPc. bv_solve. Qed.

Definition writeSuccess156d4PrefixObservations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d4Trace1 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d4Trace2 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d4Trace3 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d4Trace4 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d4Trace5 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d4Trace6 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d4Trace7
       (<["x1" := RVal_Bits writeSuccess156d4Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d4Trace8
       (writeSuccess156d4Regs regs)) global].

Definition writeSuccess156d4Observations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  writeSuccess156d4PrefixObservations regs global ++
  [writeSuccess15694Observation
     (writeSuccess156d4After regs global).1 global].

Lemma segment_156d4_mstatus (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d4)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d4 = Some a156d4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d8 = Some a156d8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156d4Before regs global)
    (writeSuccess156d4Observations regs global)
    (writeSuccess156d4After regs global) /\
  (writeSuccess156d4After regs global).1.(seq_regs) =
    writeSuccess156d4Regs regs /\
  (writeSuccess156d4After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156d4Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156d4Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156d4Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156d4), a156d4.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156d4PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156d4Before, writeSuccess156d4Trace1,
        writeSuccessTraceTail, a156d4. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess156d4Trace1, writeSuccessTraceTail, a156d4. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156d4Trace2, writeSuccess156d4Trace1,
        writeSuccessTraceTail, a156d4. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156d4). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x156d4))
        (value := RVal_Bits (Z_to_bv 64 0x156d4)).
      - reflexivity.
      - unfold writeSuccess156d4Trace3, writeSuccess156d4Trace2,
          writeSuccess156d4Trace1, writeSuccessTraceTail, a156d4. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156d4Trace5, writeSuccess156d4Trace4,
        writeSuccess156d4Trace3, writeSuccess156d4Trace2,
        writeSuccess156d4Trace1, writeSuccess156d4NextPc,
        writeSuccessTraceTail, a156d4. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x156d4 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156d4Trace5, writeSuccess156d4Trace4,
        writeSuccess156d4Trace3, writeSuccess156d4Trace2,
        writeSuccess156d4Trace1, writeSuccess156d4Link,
        writeSuccessTraceTail, a156d4. cbn.
      eapply DefineConstS with
        (v := Val_Bits
          (Z_to_bv 64 0x156d4 + BV 64 0x0)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX1)
        (value := RVal_Bits writeSuccess156d4Link)
        (updated := RVal_Bits writeSuccess156d4Link).
      - reflexivity.
      - unfold writeSuccess156d4Trace6, writeSuccess156d4Trace5,
          writeSuccess156d4Link, writeSuccess156d4Trace4,
          writeSuccess156d4Trace3, writeSuccess156d4Trace2,
          writeSuccess156d4Trace1, writeSuccessTraceTail, a156d4. cbn.
        constructor.
      - exact Hx12.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x156d4))
        (value := RVal_Bits writeSuccess156d4NextPc)
        (updated := RVal_Bits writeSuccess156d4NextPc).
      - reflexivity.
      - unfold writeSuccess156d4Trace7, writeSuccess156d4Trace6,
          writeSuccess156d4Trace5,
          writeSuccess156d4Trace4, writeSuccess156d4Trace3,
          writeSuccess156d4Trace2, writeSuccess156d4Trace1,
          writeSuccessTraceTail, a156d4. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156d8) (trace := a156d8).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x156d8).
      unfold writeSuccess156d4Regs. rewrite lookup_insert.
      rewrite writeSuccess156d4NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156d8), a156d8.
    cbn. unfold writeSuccess156d4Regs. rewrite lookup_insert.
    rewrite writeSuccess156d4NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_156d4 (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d4)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d4 = Some a156d4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d8 = Some a156d8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156d4Before regs global)
    (writeSuccess156d4Observations regs global)
    (writeSuccess156d4After regs global) /\
  (writeSuccess156d4After regs global).1.(seq_regs) =
    writeSuccess156d4Regs regs /\
  (writeSuccess156d4After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156d4Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  eapply segment_156d4_mstatus; eauto.
Qed.

Print Assumptions segment_156d4_mstatus.
Print Assumptions segment_156d4.
Print Assumptions writeSuccess156d4RegsLookupOther.
Print Assumptions writeSuccess156d4RegsDom.
