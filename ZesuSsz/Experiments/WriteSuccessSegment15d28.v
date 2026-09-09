From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d28.
Require Import IslaTraces.write_success_01.a10190.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess15d28Alignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x1" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 0x46c)) Mk_annot]
        Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Definition writeSuccess15d28Ra : bv 64 := writeSuccess15d24Link.
Definition writeSuccess15d28Link : bv 64 :=
  (Z_to_bv 64 0x15d28 + BV 64 4)%bv.
Definition writeSuccess15d28Target : bv 64 :=
  (writeSuccess15d28Ra + BV 64 0x46c)%bv.
Definition writeSuccess15d28TargetMasked : bv 64 :=
  bv_or (bv_and writeSuccess15d28Target (BV 64 0xfffffffffffffffe))
    (BV 64 0).
Definition writeSuccess15d28TargetBit : bv 1 :=
  bv_extract 0 1
    (bv_shiftr writeSuccess15d28TargetMasked (BV 64 1)).

Definition writeSuccess15d28Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a15d28).
Definition writeSuccess15d28Trace2 := writeSuccessTraceTail writeSuccess15d28Trace1.
Definition writeSuccess15d28Trace3 :=
  subst_trace (Val_Bits writeSuccess15d28Ra) 3
    (writeSuccessTraceTail writeSuccess15d28Trace2).
Definition writeSuccess15d28Trace4 := writeSuccessTraceTail writeSuccess15d28Trace3.
Definition writeSuccess15d28Trace5 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15d28)) 4
    (writeSuccessTraceTail writeSuccess15d28Trace4).
Definition writeSuccess15d28Trace6 := writeSuccessTraceTail writeSuccess15d28Trace5.
Definition writeSuccess15d28Trace7 :=
  subst_trace (Val_Bits writeSuccess15d28Link) 5
    (writeSuccessTraceTail writeSuccess15d28Trace6).
Definition writeSuccess15d28Trace8 := writeSuccessTraceTail writeSuccess15d28Trace7.
Definition writeSuccess15d28Trace9 :=
  subst_trace (Val_Bits writeSuccess15d28TargetMasked) 7
    (writeSuccessTraceTail writeSuccess15d28Trace8).
Definition writeSuccess15d28Trace10 :=
  subst_trace (Val_Bits writeSuccess15d28TargetBit) 8
    (writeSuccessTraceTail writeSuccess15d28Trace9).
Definition writeSuccess15d28Trace11 := writeSuccessTraceTail writeSuccess15d28Trace10.
Definition writeSuccess15d28Trace12 := writeSuccessTraceTail writeSuccess15d28Trace11.

Definition writeSuccess15d28Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess15d28TargetMasked]>
    (<["x1" := RVal_Bits writeSuccess15d28Link]> regs).
Definition writeSuccess15d28Before regs global : IslaState :=
  (writeSuccess15694Local a15d28 regs, global).
Definition writeSuccess15d28After regs global : IslaState :=
  (writeSuccess15694Local a10190 (writeSuccess15d28Regs regs), global).

Lemma writeSuccess15d28ValuesExact :
  writeSuccess15d28Ra = Z_to_bv 64 0xfd24 /\
  writeSuccess15d28Link = Z_to_bv 64 0x15d2c /\
  writeSuccess15d28Target = Z_to_bv 64 0x10190 /\
  writeSuccess15d28TargetMasked = Z_to_bv 64 0x10190.
Proof.
  vm_compute. repeat split; apply bv_eq; reflexivity.
Qed.

Lemma writeSuccess15d28AlignmentHolds regs :
  regs !! "x1" = Some (RVal_Bits writeSuccess15d28Ra) ->
  eval_a_exp regs writeSuccess15d28Alignment = Some (Val_Bool true).
Proof.
  intros Hx1. unfold writeSuccess15d28Alignment. cbn. rewrite Hx1. cbn.
  unfold writeSuccess15d28Ra, writeSuccess15d24Link. vm_compute.
  reflexivity.
Qed.

Definition writeSuccess15d28Locals regs : list seq_local_state :=
  [writeSuccess15694Local writeSuccess15d28Trace1 regs;
   writeSuccess15694Local writeSuccess15d28Trace2 regs;
   writeSuccess15694Local writeSuccess15d28Trace3 regs;
   writeSuccess15694Local writeSuccess15d28Trace4 regs;
   writeSuccess15694Local writeSuccess15d28Trace5 regs;
   writeSuccess15694Local writeSuccess15d28Trace6 regs;
   writeSuccess15694Local writeSuccess15d28Trace7 regs;
   writeSuccess15694Local writeSuccess15d28Trace8 regs;
   writeSuccess15694Local writeSuccess15d28Trace9 regs;
   writeSuccess15694Local writeSuccess15d28Trace10 regs;
   writeSuccess15694Local writeSuccess15d28Trace11
     (<["x1" := RVal_Bits writeSuccess15d28Link]> regs);
   writeSuccess15694Local writeSuccess15d28Trace12
     (writeSuccess15d28Regs regs)].
Definition writeSuccess15d28PrefixObservations regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess15d28Locals regs).
Definition writeSuccess15d28Observations regs global :=
  writeSuccess15d28PrefixObservations regs global ++
  [writeSuccess15694Observation (writeSuccess15d28After regs global).1 global].

Definition writeSuccess15d28Prefix8Observations regs global :
    list IslaMicroObservation :=
  map (fun local => {| microLabels := []; microAfter := (local, global) |})
    (firstn 8 (writeSuccess15d28Locals regs)).

Definition writeSuccess15d28TailObservations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d28Trace9 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d28Trace10 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d28Trace11
       (<["x1" := RVal_Bits writeSuccess15d28Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d28Trace12
       (writeSuccess15d28Regs regs)) global;
   writeSuccess15694Observation (writeSuccess15d28After regs global).1 global].

Definition writeSuccess15d28TailFirst2Observations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d28Trace9 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d28Trace10 regs) global].

Definition writeSuccess15d28TailLastObservations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d28Trace11
       (<["x1" := RVal_Bits writeSuccess15d28Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d28Trace12
       (writeSuccess15d28Regs regs)) global;
   writeSuccess15694Observation (writeSuccess15d28After regs global).1 global].

Lemma writeSuccess15d28TailObservationsSplit regs global :
  writeSuccess15d28TailObservations regs global =
    writeSuccess15d28TailFirst2Observations regs global ++
    writeSuccess15d28TailLastObservations regs global.
Proof. reflexivity. Qed.

Lemma writeSuccess15d28ObservationsSplit regs global :
  writeSuccess15d28Observations regs global =
    writeSuccess15d28Prefix8Observations regs global ++
    writeSuccess15d28TailObservations regs global.
Proof. reflexivity. Qed.

Lemma segment_15d28_mstatus regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d28)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess15d28Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d28 = Some a15d28 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d28Before regs global)
    (writeSuccess15d28Observations regs global)
    (writeSuccess15d28After regs global) /\
  (writeSuccess15d28After regs global).1.(seq_regs) = writeSuccess15d28Regs regs /\
  (writeSuccess15d28After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15d28Observations regs global)) = [].
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus.
  have Halign := writeSuccess15d28AlignmentHolds regs Hx1.
  split; [|repeat split; reflexivity].
  unfold writeSuccess15d28Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess15d28Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15d28), a15d28.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess15d28PrefixObservations, writeSuccess15d28Locals. cbn.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess15d28Before,
        writeSuccess15d28Trace1, writeSuccessTraceTail, a15d28. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess15d28Trace1,
        writeSuccessTraceTail, a15d28. cbn. apply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess15d28Trace2,
        writeSuccess15d28Trace1, writeSuccessTraceTail, a15d28. cbn.
      apply DeclareConstBitVecS' with (b := writeSuccess15d28Ra). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess15d28Trace3,
        writeSuccess15d28Trace2, writeSuccess15d28Trace1,
        writeSuccessTraceTail, a15d28. cbn. apply AssumeS. exact Halign. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess15d28Trace4,
        writeSuccess15d28Trace3, writeSuccess15d28Trace2,
        writeSuccess15d28Trace1, writeSuccessTraceTail, a15d28. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15d28). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits (Z_to_bv 64 0x15d28))
        (value := RVal_Bits (Z_to_bv 64 0x15d28)).
      - reflexivity.
      - unfold writeSuccess15d28Trace5, writeSuccess15d28Trace4,
          writeSuccess15d28Trace3, writeSuccess15d28Trace2,
          writeSuccess15d28Trace1, writeSuccessTraceTail, a15d28. cbn. constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess15d28Trace6,
        writeSuccess15d28Trace5, writeSuccess15d28Trace4,
        writeSuccess15d28Trace3, writeSuccess15d28Trace2,
        writeSuccess15d28Trace1, writeSuccess15d28Link,
        writeSuccessTraceTail, a15d28. cbn.
      eapply DefineConstS with (v := Val_Bits (Z_to_bv 64 0x15d28 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits writeSuccess15d28Ra)
        (value := RVal_Bits writeSuccess15d28Ra).
      - reflexivity.
      - unfold writeSuccess15d28Trace7, writeSuccess15d28Trace6,
          writeSuccess15d28Trace5, writeSuccess15d28Trace4,
          writeSuccess15d28Trace3, writeSuccess15d28Trace2,
          writeSuccess15d28Trace1, writeSuccessTraceTail, a15d28. cbn. constructor.
      - exact Hx1.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess15d28Trace8,
        writeSuccess15d28Trace7, writeSuccess15d28Trace6,
        writeSuccess15d28Trace5, writeSuccess15d28Trace4,
        writeSuccess15d28Trace3, writeSuccess15d28Trace2,
        writeSuccess15d28Trace1, writeSuccess15d28TargetMasked,
        writeSuccess15d28Target, writeSuccessTraceTail, a15d28. cbn.
      eapply DefineConstS with
        (v := Val_Bits writeSuccess15d28TargetMasked).
      unfold writeSuccess15d28TargetMasked, writeSuccess15d28Target.
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess15d28Trace9,
        writeSuccess15d28Trace8, writeSuccess15d28Trace7,
        writeSuccess15d28Trace6, writeSuccess15d28Trace5,
        writeSuccess15d28Trace4, writeSuccess15d28Trace3,
        writeSuccess15d28Trace2, writeSuccess15d28Trace1,
        writeSuccess15d28TargetBit, writeSuccessTraceTail, a15d28. cbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess15d28TargetBit).
      unfold writeSuccess15d28TargetBit, writeSuccess15d28TargetMasked,
        writeSuccess15d28Target. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits writeSuccess15d28Ra)
        (value := RVal_Bits writeSuccess15d28Link)
        (updated := RVal_Bits writeSuccess15d28Link).
      - reflexivity.
      - unfold writeSuccess15d28Trace10, writeSuccess15d28Trace9,
          writeSuccess15d28Trace8, writeSuccess15d28Trace7,
          writeSuccess15d28Trace6, writeSuccess15d28Trace5,
          writeSuccess15d28Trace4, writeSuccess15d28Trace3,
          writeSuccess15d28Trace2, writeSuccess15d28Trace1,
          writeSuccessTraceTail, a15d28. cbn. constructor.
      - exact Hx1.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits (Z_to_bv 64 0x15d28))
        (value := RVal_Bits writeSuccess15d28TargetMasked)
        (updated := RVal_Bits writeSuccess15d28TargetMasked).
      - reflexivity.
      - unfold writeSuccess15d28Trace11, writeSuccess15d28Trace10,
          writeSuccess15d28Trace9, writeSuccess15d28Trace8,
          writeSuccess15d28Trace7, writeSuccess15d28Trace6,
          writeSuccess15d28Trace5, writeSuccess15d28Trace4,
          writeSuccess15d28Trace3, writeSuccess15d28Trace2,
          writeSuccess15d28Trace1, writeSuccessTraceTail, a15d28. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a10190) (trace := a10190);
      try reflexivity; try constructor.
    exists (Z_to_bv 64 0x10190). unfold writeSuccess15d28Regs.
    rewrite lookup_insert. destruct writeSuccess15d28ValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x10190), a10190.
    cbn. unfold writeSuccess15d28Regs. rewrite lookup_insert.
    destruct writeSuccess15d28ValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget Hnext. repeat split; reflexivity.
Qed.

Print Assumptions segment_15d28_mstatus.

Lemma segment_15d28 regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d28)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess15d28Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d28 = Some a15d28 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d28Before regs global)
    (writeSuccess15d28Observations regs global)
    (writeSuccess15d28After regs global) /\
  (writeSuccess15d28After regs global).1.(seq_regs) = writeSuccess15d28Regs regs /\
  (writeSuccess15d28After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15d28Observations regs global)) = [].
Proof.
  exact (segment_15d28_mstatus regs global).
Qed.

Lemma writeSuccess15d28RegsLookupOther regs reg :
  reg <> "PC" -> reg <> "x1" ->
  writeSuccess15d28Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx1. unfold writeSuccess15d28Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence. reflexivity.
Qed.

Lemma writeSuccess15d28RegsDom regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d28)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess15d28Ra) ->
  dom (writeSuccess15d28Regs regs) = dom regs.
Proof.
  intros Hpc Hx1. apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx1.
  unfold writeSuccess15d28Regs. rewrite !dom_insert_L. set_solver.
Qed.


Print Assumptions segment_15d28.
Print Assumptions writeSuccess15d28RegsLookupOther.
Print Assumptions writeSuccess15d28RegsDom.
