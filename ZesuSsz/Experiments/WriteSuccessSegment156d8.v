From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_94.a156d8.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156d8Alignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x1" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 0x63c)) Mk_annot]
        Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Definition writeSuccess156d8Ra : bv 64 := writeSuccess156d4Link.
Definition writeSuccess156d8Link : bv 64 :=
  (Z_to_bv 64 0x156d8 + BV 64 4)%bv.
Definition writeSuccess156d8Target : bv 64 :=
  (writeSuccess156d8Ra + BV 64 0x63c)%bv.
Definition writeSuccess156d8TargetMasked : bv 64 :=
  bv_or (bv_and writeSuccess156d8Target (BV 64 0xfffffffffffffffe))
    (BV 64 0).
Definition writeSuccess156d8TargetBit : bv 1 :=
  bv_extract 0 1
    (bv_shiftr writeSuccess156d8TargetMasked (BV 64 1)).

Definition writeSuccess156d8Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156d8).
Definition writeSuccess156d8Trace2 := writeSuccessTraceTail writeSuccess156d8Trace1.
Definition writeSuccess156d8Trace3 :=
  subst_trace (Val_Bits writeSuccess156d8Ra) 3
    (writeSuccessTraceTail writeSuccess156d8Trace2).
Definition writeSuccess156d8Trace4 := writeSuccessTraceTail writeSuccess156d8Trace3.
Definition writeSuccess156d8Trace5 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156d8)) 4
    (writeSuccessTraceTail writeSuccess156d8Trace4).
Definition writeSuccess156d8Trace6 := writeSuccessTraceTail writeSuccess156d8Trace5.
Definition writeSuccess156d8Trace7 :=
  subst_trace (Val_Bits writeSuccess156d8Link) 5
    (writeSuccessTraceTail writeSuccess156d8Trace6).
Definition writeSuccess156d8Trace8 := writeSuccessTraceTail writeSuccess156d8Trace7.
Definition writeSuccess156d8Trace9 :=
  subst_trace (Val_Bits writeSuccess156d8TargetMasked) 7
    (writeSuccessTraceTail writeSuccess156d8Trace8).
Definition writeSuccess156d8Trace10 :=
  subst_trace (Val_Bits writeSuccess156d8TargetBit) 8
    (writeSuccessTraceTail writeSuccess156d8Trace9).
Definition writeSuccess156d8Trace11 := writeSuccessTraceTail writeSuccess156d8Trace10.
Definition writeSuccess156d8Trace12 := writeSuccessTraceTail writeSuccess156d8Trace11.

Definition writeSuccess156d8Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156d8TargetMasked]>
    (<["x1" := RVal_Bits writeSuccess156d8Link]> regs).
Definition writeSuccess156d8Before regs global : IslaState :=
  (writeSuccess15694Local a156d8 regs, global).
Definition writeSuccess156d8After regs global : IslaState :=
  (writeSuccess15694Local a15d10 (writeSuccess156d8Regs regs), global).

Lemma writeSuccess156d8ValuesExact :
  writeSuccess156d8Ra = Z_to_bv 64 0x156d4 /\
  writeSuccess156d8Link = Z_to_bv 64 0x156dc /\
  writeSuccess156d8Target = Z_to_bv 64 0x15d10 /\
  writeSuccess156d8TargetMasked = Z_to_bv 64 0x15d10.
Proof.
  vm_compute. repeat split; apply bv_eq; reflexivity.
Qed.

Lemma writeSuccess156d8AlignmentHolds regs :
  regs !! "x1" = Some (RVal_Bits writeSuccess156d8Ra) ->
  eval_a_exp regs writeSuccess156d8Alignment = Some (Val_Bool true).
Proof.
  intros Hx1. unfold writeSuccess156d8Alignment. cbn. rewrite Hx1. cbn.
  unfold writeSuccess156d8Ra, writeSuccess156d4Link. vm_compute.
  reflexivity.
Qed.

Definition writeSuccess156d8Locals regs : list seq_local_state :=
  [writeSuccess15694Local writeSuccess156d8Trace1 regs;
   writeSuccess15694Local writeSuccess156d8Trace2 regs;
   writeSuccess15694Local writeSuccess156d8Trace3 regs;
   writeSuccess15694Local writeSuccess156d8Trace4 regs;
   writeSuccess15694Local writeSuccess156d8Trace5 regs;
   writeSuccess15694Local writeSuccess156d8Trace6 regs;
   writeSuccess15694Local writeSuccess156d8Trace7 regs;
   writeSuccess15694Local writeSuccess156d8Trace8 regs;
   writeSuccess15694Local writeSuccess156d8Trace9 regs;
   writeSuccess15694Local writeSuccess156d8Trace10 regs;
   writeSuccess15694Local writeSuccess156d8Trace11
     (<["x1" := RVal_Bits writeSuccess156d8Link]> regs);
   writeSuccess15694Local writeSuccess156d8Trace12
     (writeSuccess156d8Regs regs)].
Definition writeSuccess156d8PrefixObservations regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess156d8Locals regs).
Definition writeSuccess156d8Observations regs global :=
  writeSuccess156d8PrefixObservations regs global ++
  [writeSuccess15694Observation (writeSuccess156d8After regs global).1 global].

Definition writeSuccess156d8Prefix8Observations regs global :
    list IslaMicroObservation :=
  map (fun local => {| microLabels := []; microAfter := (local, global) |})
    (firstn 8 (writeSuccess156d8Locals regs)).

Definition writeSuccess156d8TailObservations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d8Trace9 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d8Trace10 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d8Trace11
       (<["x1" := RVal_Bits writeSuccess156d8Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d8Trace12
       (writeSuccess156d8Regs regs)) global;
   writeSuccess15694Observation (writeSuccess156d8After regs global).1 global].

Definition writeSuccess156d8TailFirst2Observations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d8Trace9 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d8Trace10 regs) global].

Definition writeSuccess156d8TailLastObservations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d8Trace11
       (<["x1" := RVal_Bits writeSuccess156d8Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156d8Trace12
       (writeSuccess156d8Regs regs)) global;
   writeSuccess15694Observation (writeSuccess156d8After regs global).1 global].

Lemma writeSuccess156d8TailObservationsSplit regs global :
  writeSuccess156d8TailObservations regs global =
    writeSuccess156d8TailFirst2Observations regs global ++
    writeSuccess156d8TailLastObservations regs global.
Proof. reflexivity. Qed.

Lemma writeSuccess156d8ObservationsSplit regs global :
  writeSuccess156d8Observations regs global =
    writeSuccess156d8Prefix8Observations regs global ++
    writeSuccess156d8TailObservations regs global.
Proof. reflexivity. Qed.

Lemma segment_156d8_mstatus regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d8)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156d8Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d8 = Some a156d8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156d8Before regs global)
    (writeSuccess156d8Observations regs global)
    (writeSuccess156d8After regs global) /\
  (writeSuccess156d8After regs global).1.(seq_regs) = writeSuccess156d8Regs regs /\
  (writeSuccess156d8After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156d8Observations regs global)) = [].
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus.
  have Halign := writeSuccess156d8AlignmentHolds regs Hx1.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156d8Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156d8Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156d8), a156d8.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156d8PrefixObservations, writeSuccess156d8Locals. cbn.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156d8Before,
        writeSuccess156d8Trace1, writeSuccessTraceTail, a156d8. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess156d8Trace1,
        writeSuccessTraceTail, a156d8. cbn. apply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156d8Trace2,
        writeSuccess156d8Trace1, writeSuccessTraceTail, a156d8. cbn.
      apply DeclareConstBitVecS' with (b := writeSuccess156d8Ra). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess156d8Trace3,
        writeSuccess156d8Trace2, writeSuccess156d8Trace1,
        writeSuccessTraceTail, a156d8. cbn. apply AssumeS. exact Halign. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156d8Trace4,
        writeSuccess156d8Trace3, writeSuccess156d8Trace2,
        writeSuccess156d8Trace1, writeSuccessTraceTail, a156d8. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156d8). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits (Z_to_bv 64 0x156d8))
        (value := RVal_Bits (Z_to_bv 64 0x156d8)).
      - reflexivity.
      - unfold writeSuccess156d8Trace5, writeSuccess156d8Trace4,
          writeSuccess156d8Trace3, writeSuccess156d8Trace2,
          writeSuccess156d8Trace1, writeSuccessTraceTail, a156d8. cbn. constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156d8Trace6,
        writeSuccess156d8Trace5, writeSuccess156d8Trace4,
        writeSuccess156d8Trace3, writeSuccess156d8Trace2,
        writeSuccess156d8Trace1, writeSuccess156d8Link,
        writeSuccessTraceTail, a156d8. cbn.
      eapply DefineConstS with (v := Val_Bits (Z_to_bv 64 0x156d8 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits writeSuccess156d8Ra)
        (value := RVal_Bits writeSuccess156d8Ra).
      - reflexivity.
      - unfold writeSuccess156d8Trace7, writeSuccess156d8Trace6,
          writeSuccess156d8Trace5, writeSuccess156d8Trace4,
          writeSuccess156d8Trace3, writeSuccess156d8Trace2,
          writeSuccess156d8Trace1, writeSuccessTraceTail, a156d8. cbn. constructor.
      - exact Hx1.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156d8Trace8,
        writeSuccess156d8Trace7, writeSuccess156d8Trace6,
        writeSuccess156d8Trace5, writeSuccess156d8Trace4,
        writeSuccess156d8Trace3, writeSuccess156d8Trace2,
        writeSuccess156d8Trace1, writeSuccess156d8TargetMasked,
        writeSuccess156d8Target, writeSuccessTraceTail, a156d8. cbn.
      eapply DefineConstS with
        (v := Val_Bits writeSuccess156d8TargetMasked).
      unfold writeSuccess156d8TargetMasked, writeSuccess156d8Target.
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156d8Trace9,
        writeSuccess156d8Trace8, writeSuccess156d8Trace7,
        writeSuccess156d8Trace6, writeSuccess156d8Trace5,
        writeSuccess156d8Trace4, writeSuccess156d8Trace3,
        writeSuccess156d8Trace2, writeSuccess156d8Trace1,
        writeSuccess156d8TargetBit, writeSuccessTraceTail, a156d8. cbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess156d8TargetBit).
      unfold writeSuccess156d8TargetBit, writeSuccess156d8TargetMasked,
        writeSuccess156d8Target. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits writeSuccess156d8Ra)
        (value := RVal_Bits writeSuccess156d8Link)
        (updated := RVal_Bits writeSuccess156d8Link).
      - reflexivity.
      - unfold writeSuccess156d8Trace10, writeSuccess156d8Trace9,
          writeSuccess156d8Trace8, writeSuccess156d8Trace7,
          writeSuccess156d8Trace6, writeSuccess156d8Trace5,
          writeSuccess156d8Trace4, writeSuccess156d8Trace3,
          writeSuccess156d8Trace2, writeSuccess156d8Trace1,
          writeSuccessTraceTail, a156d8. cbn. constructor.
      - exact Hx1.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits (Z_to_bv 64 0x156d8))
        (value := RVal_Bits writeSuccess156d8TargetMasked)
        (updated := RVal_Bits writeSuccess156d8TargetMasked).
      - reflexivity.
      - unfold writeSuccess156d8Trace11, writeSuccess156d8Trace10,
          writeSuccess156d8Trace9, writeSuccess156d8Trace8,
          writeSuccess156d8Trace7, writeSuccess156d8Trace6,
          writeSuccess156d8Trace5, writeSuccess156d8Trace4,
          writeSuccess156d8Trace3, writeSuccess156d8Trace2,
          writeSuccess156d8Trace1, writeSuccessTraceTail, a156d8. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15d10) (trace := a15d10);
      try reflexivity; try constructor.
    exists (Z_to_bv 64 0x15d10). unfold writeSuccess156d8Regs.
    rewrite lookup_insert. destruct writeSuccess156d8ValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15d10), a15d10.
    cbn. unfold writeSuccess156d8Regs. rewrite lookup_insert.
    destruct writeSuccess156d8ValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget Hnext. repeat split; reflexivity.
Qed.

Print Assumptions segment_156d8_mstatus.

Lemma segment_156d8 regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d8)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156d8Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d8 = Some a156d8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  writeSuccessTraceAssumptions (writeSuccess156d8Before regs global) ->
  IslaInstructionSegment (writeSuccess156d8Before regs global)
    (writeSuccess156d8Observations regs global)
    (writeSuccess156d8After regs global) /\
  (writeSuccess156d8After regs global).1.(seq_regs) = writeSuccess156d8Regs regs /\
  (writeSuccess156d8After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156d8Observations regs global)) = [].
Proof.
  intros Hpc Hx1 Hcode Hnext Hassumptions.
  eapply segment_156d8_mstatus; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Lemma writeSuccess156d8RegsLookupOther regs reg :
  reg <> "PC" -> reg <> "x1" ->
  writeSuccess156d8Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx1. unfold writeSuccess156d8Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence. reflexivity.
Qed.

Lemma writeSuccess156d8RegsDom regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d8)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156d8Ra) ->
  dom (writeSuccess156d8Regs regs) = dom regs.
Proof.
  intros Hpc Hx1. apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx1.
  unfold writeSuccess156d8Regs. rewrite !dom_insert_L. set_solver.
Qed.


Print Assumptions segment_156d8.
Print Assumptions writeSuccess156d8RegsLookupOther.
Print Assumptions writeSuccess156d8RegsDom.
