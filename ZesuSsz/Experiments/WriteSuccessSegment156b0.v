From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156b0.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ac.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156b0Alignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x1" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 0x664)) Mk_annot]
        Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Definition writeSuccess156b0Ra : bv 64 := writeSuccess156acLink.
Definition writeSuccess156b0Link : bv 64 :=
  (Z_to_bv 64 0x156b0 + BV 64 4)%bv.
Definition writeSuccess156b0Target : bv 64 :=
  (writeSuccess156b0Ra + BV 64 0x664)%bv.
Definition writeSuccess156b0TargetMasked : bv 64 :=
  bv_or (bv_and writeSuccess156b0Target (BV 64 0xfffffffffffffffe))
    (BV 64 0).
Definition writeSuccess156b0TargetBit : bv 1 :=
  bv_extract 0 1
    (bv_shiftr writeSuccess156b0TargetMasked (BV 64 1)).

Definition writeSuccess156b0Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156b0).
Definition writeSuccess156b0Trace2 := writeSuccessTraceTail writeSuccess156b0Trace1.
Definition writeSuccess156b0Trace3 :=
  subst_trace (Val_Bits writeSuccess156b0Ra) 3
    (writeSuccessTraceTail writeSuccess156b0Trace2).
Definition writeSuccess156b0Trace4 := writeSuccessTraceTail writeSuccess156b0Trace3.
Definition writeSuccess156b0Trace5 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156b0)) 4
    (writeSuccessTraceTail writeSuccess156b0Trace4).
Definition writeSuccess156b0Trace6 := writeSuccessTraceTail writeSuccess156b0Trace5.
Definition writeSuccess156b0Trace7 :=
  subst_trace (Val_Bits writeSuccess156b0Link) 5
    (writeSuccessTraceTail writeSuccess156b0Trace6).
Definition writeSuccess156b0Trace8 := writeSuccessTraceTail writeSuccess156b0Trace7.
Definition writeSuccess156b0Trace9 :=
  subst_trace (Val_Bits writeSuccess156b0TargetMasked) 7
    (writeSuccessTraceTail writeSuccess156b0Trace8).
Definition writeSuccess156b0Trace10 :=
  subst_trace (Val_Bits writeSuccess156b0TargetBit) 8
    (writeSuccessTraceTail writeSuccess156b0Trace9).
Definition writeSuccess156b0Trace11 := writeSuccessTraceTail writeSuccess156b0Trace10.
Definition writeSuccess156b0Trace12 := writeSuccessTraceTail writeSuccess156b0Trace11.

Definition writeSuccess156b0Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156b0TargetMasked]>
    (<["x1" := RVal_Bits writeSuccess156b0Link]> regs).
Definition writeSuccess156b0Before regs global : IslaState :=
  (writeSuccess15694Local a156b0 regs, global).
Definition writeSuccess156b0After regs global : IslaState :=
  (writeSuccess15694Local a15d10 (writeSuccess156b0Regs regs), global).

Lemma writeSuccess156b0ValuesExact :
  writeSuccess156b0Ra = Z_to_bv 64 0x156ac /\
  writeSuccess156b0Link = Z_to_bv 64 0x156b4 /\
  writeSuccess156b0Target = Z_to_bv 64 0x15d10 /\
  writeSuccess156b0TargetMasked = Z_to_bv 64 0x15d10.
Proof.
  vm_compute. repeat split; apply bv_eq; reflexivity.
Qed.

Lemma writeSuccess156b0AlignmentHolds regs :
  regs !! "x1" = Some (RVal_Bits writeSuccess156b0Ra) ->
  eval_a_exp regs writeSuccess156b0Alignment = Some (Val_Bool true).
Proof.
  intros Hx1. unfold writeSuccess156b0Alignment. cbn. rewrite Hx1. cbn.
  unfold writeSuccess156b0Ra, writeSuccess156acLink. vm_compute.
  reflexivity.
Qed.

Definition writeSuccess156b0Locals regs : list seq_local_state :=
  [writeSuccess15694Local writeSuccess156b0Trace1 regs;
   writeSuccess15694Local writeSuccess156b0Trace2 regs;
   writeSuccess15694Local writeSuccess156b0Trace3 regs;
   writeSuccess15694Local writeSuccess156b0Trace4 regs;
   writeSuccess15694Local writeSuccess156b0Trace5 regs;
   writeSuccess15694Local writeSuccess156b0Trace6 regs;
   writeSuccess15694Local writeSuccess156b0Trace7 regs;
   writeSuccess15694Local writeSuccess156b0Trace8 regs;
   writeSuccess15694Local writeSuccess156b0Trace9 regs;
   writeSuccess15694Local writeSuccess156b0Trace10 regs;
   writeSuccess15694Local writeSuccess156b0Trace11
     (<["x1" := RVal_Bits writeSuccess156b0Link]> regs);
   writeSuccess15694Local writeSuccess156b0Trace12
     (writeSuccess156b0Regs regs)].
Definition writeSuccess156b0PrefixObservations regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess156b0Locals regs).
Definition writeSuccess156b0Observations regs global :=
  writeSuccess156b0PrefixObservations regs global ++
  [writeSuccess15694Observation (writeSuccess156b0After regs global).1 global].

Definition writeSuccess156b0Prefix8Observations regs global :
    list IslaMicroObservation :=
  map (fun local => {| microLabels := []; microAfter := (local, global) |})
    (firstn 8 (writeSuccess156b0Locals regs)).

Definition writeSuccess156b0TailObservations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b0Trace9 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b0Trace10 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b0Trace11
       (<["x1" := RVal_Bits writeSuccess156b0Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b0Trace12
       (writeSuccess156b0Regs regs)) global;
   writeSuccess15694Observation (writeSuccess156b0After regs global).1 global].

Definition writeSuccess156b0TailFirst2Observations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b0Trace9 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b0Trace10 regs) global].

Definition writeSuccess156b0TailLastObservations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b0Trace11
       (<["x1" := RVal_Bits writeSuccess156b0Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156b0Trace12
       (writeSuccess156b0Regs regs)) global;
   writeSuccess15694Observation (writeSuccess156b0After regs global).1 global].

Lemma writeSuccess156b0TailObservationsSplit regs global :
  writeSuccess156b0TailObservations regs global =
    writeSuccess156b0TailFirst2Observations regs global ++
    writeSuccess156b0TailLastObservations regs global.
Proof. reflexivity. Qed.

Lemma writeSuccess156b0ObservationsSplit regs global :
  writeSuccess156b0Observations regs global =
    writeSuccess156b0Prefix8Observations regs global ++
    writeSuccess156b0TailObservations regs global.
Proof. reflexivity. Qed.

Lemma segment_156b0_mstatus regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b0)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156b0Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156b0Before regs global)
    (writeSuccess156b0Observations regs global)
    (writeSuccess156b0After regs global) /\
  (writeSuccess156b0After regs global).1.(seq_regs) = writeSuccess156b0Regs regs /\
  (writeSuccess156b0After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156b0Observations regs global)) = [].
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus.
  have Halign := writeSuccess156b0AlignmentHolds regs Hx1.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156b0Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156b0Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156b0), a156b0.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156b0PrefixObservations, writeSuccess156b0Locals. cbn.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156b0Before,
        writeSuccess156b0Trace1, writeSuccessTraceTail, a156b0. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess156b0Trace1,
        writeSuccessTraceTail, a156b0. cbn. apply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156b0Trace2,
        writeSuccess156b0Trace1, writeSuccessTraceTail, a156b0. cbn.
      apply DeclareConstBitVecS' with (b := writeSuccess156b0Ra). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess156b0Trace3,
        writeSuccess156b0Trace2, writeSuccess156b0Trace1,
        writeSuccessTraceTail, a156b0. cbn. apply AssumeS. exact Halign. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156b0Trace4,
        writeSuccess156b0Trace3, writeSuccess156b0Trace2,
        writeSuccess156b0Trace1, writeSuccessTraceTail, a156b0. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156b0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits (Z_to_bv 64 0x156b0))
        (value := RVal_Bits (Z_to_bv 64 0x156b0)).
      - reflexivity.
      - unfold writeSuccess156b0Trace5, writeSuccess156b0Trace4,
          writeSuccess156b0Trace3, writeSuccess156b0Trace2,
          writeSuccess156b0Trace1, writeSuccessTraceTail, a156b0. cbn. constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156b0Trace6,
        writeSuccess156b0Trace5, writeSuccess156b0Trace4,
        writeSuccess156b0Trace3, writeSuccess156b0Trace2,
        writeSuccess156b0Trace1, writeSuccess156b0Link,
        writeSuccessTraceTail, a156b0. cbn.
      eapply DefineConstS with (v := Val_Bits (Z_to_bv 64 0x156b0 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits writeSuccess156b0Ra)
        (value := RVal_Bits writeSuccess156b0Ra).
      - reflexivity.
      - unfold writeSuccess156b0Trace7, writeSuccess156b0Trace6,
          writeSuccess156b0Trace5, writeSuccess156b0Trace4,
          writeSuccess156b0Trace3, writeSuccess156b0Trace2,
          writeSuccess156b0Trace1, writeSuccessTraceTail, a156b0. cbn. constructor.
      - exact Hx1.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156b0Trace8,
        writeSuccess156b0Trace7, writeSuccess156b0Trace6,
        writeSuccess156b0Trace5, writeSuccess156b0Trace4,
        writeSuccess156b0Trace3, writeSuccess156b0Trace2,
        writeSuccess156b0Trace1, writeSuccess156b0TargetMasked,
        writeSuccess156b0Target, writeSuccessTraceTail, a156b0. cbn.
      eapply DefineConstS with
        (v := Val_Bits writeSuccess156b0TargetMasked).
      unfold writeSuccess156b0TargetMasked, writeSuccess156b0Target.
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156b0Trace9,
        writeSuccess156b0Trace8, writeSuccess156b0Trace7,
        writeSuccess156b0Trace6, writeSuccess156b0Trace5,
        writeSuccess156b0Trace4, writeSuccess156b0Trace3,
        writeSuccess156b0Trace2, writeSuccess156b0Trace1,
        writeSuccess156b0TargetBit, writeSuccessTraceTail, a156b0. cbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess156b0TargetBit).
      unfold writeSuccess156b0TargetBit, writeSuccess156b0TargetMasked,
        writeSuccess156b0Target. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits writeSuccess156b0Ra)
        (value := RVal_Bits writeSuccess156b0Link)
        (updated := RVal_Bits writeSuccess156b0Link).
      - reflexivity.
      - unfold writeSuccess156b0Trace10, writeSuccess156b0Trace9,
          writeSuccess156b0Trace8, writeSuccess156b0Trace7,
          writeSuccess156b0Trace6, writeSuccess156b0Trace5,
          writeSuccess156b0Trace4, writeSuccess156b0Trace3,
          writeSuccess156b0Trace2, writeSuccess156b0Trace1,
          writeSuccessTraceTail, a156b0. cbn. constructor.
      - exact Hx1.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits (Z_to_bv 64 0x156b0))
        (value := RVal_Bits writeSuccess156b0TargetMasked)
        (updated := RVal_Bits writeSuccess156b0TargetMasked).
      - reflexivity.
      - unfold writeSuccess156b0Trace11, writeSuccess156b0Trace10,
          writeSuccess156b0Trace9, writeSuccess156b0Trace8,
          writeSuccess156b0Trace7, writeSuccess156b0Trace6,
          writeSuccess156b0Trace5, writeSuccess156b0Trace4,
          writeSuccess156b0Trace3, writeSuccess156b0Trace2,
          writeSuccess156b0Trace1, writeSuccessTraceTail, a156b0. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15d10) (trace := a15d10);
      try reflexivity; try constructor.
    exists (Z_to_bv 64 0x15d10). unfold writeSuccess156b0Regs.
    rewrite lookup_insert. destruct writeSuccess156b0ValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15d10), a15d10.
    cbn. unfold writeSuccess156b0Regs. rewrite lookup_insert.
    destruct writeSuccess156b0ValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget Hnext. repeat split; reflexivity.
Qed.

Print Assumptions segment_156b0_mstatus.

Lemma segment_156b0 regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b0)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156b0Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156b0Before regs global)
    (writeSuccess156b0Observations regs global)
    (writeSuccess156b0After regs global) /\
  (writeSuccess156b0After regs global).1.(seq_regs) = writeSuccess156b0Regs regs /\
  (writeSuccess156b0After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156b0Observations regs global)) = [].
Proof.
  exact (segment_156b0_mstatus regs global).
Qed.

Lemma writeSuccess156b0RegsLookupOther regs reg :
  reg <> "PC" -> reg <> "x1" ->
  writeSuccess156b0Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx1. unfold writeSuccess156b0Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence. reflexivity.
Qed.

Lemma writeSuccess156b0RegsDom regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b0)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156b0Ra) ->
  dom (writeSuccess156b0Regs regs) = dom regs.
Proof.
  intros Hpc Hx1. apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx1.
  unfold writeSuccess156b0Regs. rewrite !dom_insert_L. set_solver.
Qed.


Print Assumptions segment_156b0.
Print Assumptions writeSuccess156b0RegsLookupOther.
Print Assumptions writeSuccess156b0RegsDom.
