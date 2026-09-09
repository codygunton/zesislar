From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a156a4.
Require Import IslaTraces.write_success_02.a101d4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156a4Alignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x1" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 0xfffffffffffffb34)) Mk_annot]
        Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Definition writeSuccess156a4Ra : bv 64 := writeSuccess156a0Link.
Definition writeSuccess156a4Link : bv 64 :=
  (Z_to_bv 64 0x156a4 + BV 64 4)%bv.
Definition writeSuccess156a4Target : bv 64 :=
  (writeSuccess156a4Ra + BV 64 0xfffffffffffffb34)%bv.
Definition writeSuccess156a4TargetMasked : bv 64 :=
  bv_or (bv_and writeSuccess156a4Target (BV 64 0xfffffffffffffffe))
    (BV 64 0).
Definition writeSuccess156a4TargetBit : bv 1 :=
  bv_extract 0 1
    (bv_shiftr writeSuccess156a4TargetMasked (BV 64 1)).

Definition writeSuccess156a4Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156a4).
Definition writeSuccess156a4Trace2 := writeSuccessTraceTail writeSuccess156a4Trace1.
Definition writeSuccess156a4Trace3 :=
  subst_trace (Val_Bits writeSuccess156a4Ra) 3
    (writeSuccessTraceTail writeSuccess156a4Trace2).
Definition writeSuccess156a4Trace4 := writeSuccessTraceTail writeSuccess156a4Trace3.
Definition writeSuccess156a4Trace5 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156a4)) 4
    (writeSuccessTraceTail writeSuccess156a4Trace4).
Definition writeSuccess156a4Trace6 := writeSuccessTraceTail writeSuccess156a4Trace5.
Definition writeSuccess156a4Trace7 :=
  subst_trace (Val_Bits writeSuccess156a4Link) 5
    (writeSuccessTraceTail writeSuccess156a4Trace6).
Definition writeSuccess156a4Trace8 := writeSuccessTraceTail writeSuccess156a4Trace7.
Definition writeSuccess156a4Trace9 :=
  subst_trace (Val_Bits writeSuccess156a4TargetMasked) 7
    (writeSuccessTraceTail writeSuccess156a4Trace8).
Definition writeSuccess156a4Trace10 :=
  subst_trace (Val_Bits writeSuccess156a4TargetBit) 8
    (writeSuccessTraceTail writeSuccess156a4Trace9).
Definition writeSuccess156a4Trace11 := writeSuccessTraceTail writeSuccess156a4Trace10.
Definition writeSuccess156a4Trace12 := writeSuccessTraceTail writeSuccess156a4Trace11.

Definition writeSuccess156a4Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156a4TargetMasked]>
    (<["x1" := RVal_Bits writeSuccess156a4Link]> regs).
Definition writeSuccess156a4Before regs global : IslaState :=
  (writeSuccess15694Local a156a4 regs, global).
Definition writeSuccess156a4After regs global : IslaState :=
  (writeSuccess15694Local a101d4 (writeSuccess156a4Regs regs), global).

Lemma writeSuccess156a4ValuesExact :
  writeSuccess156a4Ra = Z_to_bv 64 0x106a0 /\
  writeSuccess156a4Link = Z_to_bv 64 0x156a8 /\
  writeSuccess156a4Target = Z_to_bv 64 0x101d4 /\
  writeSuccess156a4TargetMasked = Z_to_bv 64 0x101d4.
Proof.
  vm_compute. repeat split; apply bv_eq; reflexivity.
Qed.

Lemma writeSuccess156a4AlignmentHolds regs :
  regs !! "x1" = Some (RVal_Bits writeSuccess156a4Ra) ->
  eval_a_exp regs writeSuccess156a4Alignment = Some (Val_Bool true).
Proof.
  intros Hx1. unfold writeSuccess156a4Alignment. cbn. rewrite Hx1. cbn.
  unfold writeSuccess156a4Ra, writeSuccess156a0Link. vm_compute.
  reflexivity.
Qed.

Definition writeSuccess156a4Locals regs : list seq_local_state :=
  [writeSuccess15694Local writeSuccess156a4Trace1 regs;
   writeSuccess15694Local writeSuccess156a4Trace2 regs;
   writeSuccess15694Local writeSuccess156a4Trace3 regs;
   writeSuccess15694Local writeSuccess156a4Trace4 regs;
   writeSuccess15694Local writeSuccess156a4Trace5 regs;
   writeSuccess15694Local writeSuccess156a4Trace6 regs;
   writeSuccess15694Local writeSuccess156a4Trace7 regs;
   writeSuccess15694Local writeSuccess156a4Trace8 regs;
   writeSuccess15694Local writeSuccess156a4Trace9 regs;
   writeSuccess15694Local writeSuccess156a4Trace10 regs;
   writeSuccess15694Local writeSuccess156a4Trace11
     (<["x1" := RVal_Bits writeSuccess156a4Link]> regs);
   writeSuccess15694Local writeSuccess156a4Trace12
     (writeSuccess156a4Regs regs)].
Definition writeSuccess156a4PrefixObservations regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess156a4Locals regs).
Definition writeSuccess156a4Observations regs global :=
  writeSuccess156a4PrefixObservations regs global ++
  [writeSuccess15694Observation (writeSuccess156a4After regs global).1 global].

Definition writeSuccess156a4Prefix8Observations regs global :
    list IslaMicroObservation :=
  map (fun local => {| microLabels := []; microAfter := (local, global) |})
    (firstn 8 (writeSuccess156a4Locals regs)).

Definition writeSuccess156a4TailObservations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a4Trace9 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a4Trace10 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a4Trace11
       (<["x1" := RVal_Bits writeSuccess156a4Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a4Trace12
       (writeSuccess156a4Regs regs)) global;
   writeSuccess15694Observation (writeSuccess156a4After regs global).1 global].

Definition writeSuccess156a4TailFirst2Observations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a4Trace9 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a4Trace10 regs) global].

Definition writeSuccess156a4TailLastObservations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a4Trace11
       (<["x1" := RVal_Bits writeSuccess156a4Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a4Trace12
       (writeSuccess156a4Regs regs)) global;
   writeSuccess15694Observation (writeSuccess156a4After regs global).1 global].

Lemma writeSuccess156a4TailObservationsSplit regs global :
  writeSuccess156a4TailObservations regs global =
    writeSuccess156a4TailFirst2Observations regs global ++
    writeSuccess156a4TailLastObservations regs global.
Proof. reflexivity. Qed.

Lemma writeSuccess156a4ObservationsSplit regs global :
  writeSuccess156a4Observations regs global =
    writeSuccess156a4Prefix8Observations regs global ++
    writeSuccess156a4TailObservations regs global.
Proof. reflexivity. Qed.

Lemma segment_156a4_mstatus regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a4)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156a4Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d4 = Some a101d4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156a4Before regs global)
    (writeSuccess156a4Observations regs global)
    (writeSuccess156a4After regs global) /\
  (writeSuccess156a4After regs global).1.(seq_regs) = writeSuccess156a4Regs regs /\
  (writeSuccess156a4After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156a4Observations regs global)) = [].
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus.
  have Halign := writeSuccess156a4AlignmentHolds regs Hx1.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156a4Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156a4Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156a4), a156a4.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156a4PrefixObservations, writeSuccess156a4Locals. cbn.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156a4Before,
        writeSuccess156a4Trace1, writeSuccessTraceTail, a156a4. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess156a4Trace1,
        writeSuccessTraceTail, a156a4. cbn. apply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156a4Trace2,
        writeSuccess156a4Trace1, writeSuccessTraceTail, a156a4. cbn.
      apply DeclareConstBitVecS' with (b := writeSuccess156a4Ra). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess156a4Trace3,
        writeSuccess156a4Trace2, writeSuccess156a4Trace1,
        writeSuccessTraceTail, a156a4. cbn. apply AssumeS. exact Halign. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156a4Trace4,
        writeSuccess156a4Trace3, writeSuccess156a4Trace2,
        writeSuccess156a4Trace1, writeSuccessTraceTail, a156a4. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156a4). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits (Z_to_bv 64 0x156a4))
        (value := RVal_Bits (Z_to_bv 64 0x156a4)).
      - reflexivity.
      - unfold writeSuccess156a4Trace5, writeSuccess156a4Trace4,
          writeSuccess156a4Trace3, writeSuccess156a4Trace2,
          writeSuccess156a4Trace1, writeSuccessTraceTail, a156a4. cbn. constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156a4Trace6,
        writeSuccess156a4Trace5, writeSuccess156a4Trace4,
        writeSuccess156a4Trace3, writeSuccess156a4Trace2,
        writeSuccess156a4Trace1, writeSuccess156a4Link,
        writeSuccessTraceTail, a156a4. cbn.
      eapply DefineConstS with (v := Val_Bits (Z_to_bv 64 0x156a4 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits writeSuccess156a4Ra)
        (value := RVal_Bits writeSuccess156a4Ra).
      - reflexivity.
      - unfold writeSuccess156a4Trace7, writeSuccess156a4Trace6,
          writeSuccess156a4Trace5, writeSuccess156a4Trace4,
          writeSuccess156a4Trace3, writeSuccess156a4Trace2,
          writeSuccess156a4Trace1, writeSuccessTraceTail, a156a4. cbn. constructor.
      - exact Hx1.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156a4Trace8,
        writeSuccess156a4Trace7, writeSuccess156a4Trace6,
        writeSuccess156a4Trace5, writeSuccess156a4Trace4,
        writeSuccess156a4Trace3, writeSuccess156a4Trace2,
        writeSuccess156a4Trace1, writeSuccess156a4TargetMasked,
        writeSuccess156a4Target, writeSuccessTraceTail, a156a4. cbn.
      eapply DefineConstS with
        (v := Val_Bits writeSuccess156a4TargetMasked).
      unfold writeSuccess156a4TargetMasked, writeSuccess156a4Target.
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156a4Trace9,
        writeSuccess156a4Trace8, writeSuccess156a4Trace7,
        writeSuccess156a4Trace6, writeSuccess156a4Trace5,
        writeSuccess156a4Trace4, writeSuccess156a4Trace3,
        writeSuccess156a4Trace2, writeSuccess156a4Trace1,
        writeSuccess156a4TargetBit, writeSuccessTraceTail, a156a4. cbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess156a4TargetBit).
      unfold writeSuccess156a4TargetBit, writeSuccess156a4TargetMasked,
        writeSuccess156a4Target. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits writeSuccess156a4Ra)
        (value := RVal_Bits writeSuccess156a4Link)
        (updated := RVal_Bits writeSuccess156a4Link).
      - reflexivity.
      - unfold writeSuccess156a4Trace10, writeSuccess156a4Trace9,
          writeSuccess156a4Trace8, writeSuccess156a4Trace7,
          writeSuccess156a4Trace6, writeSuccess156a4Trace5,
          writeSuccess156a4Trace4, writeSuccess156a4Trace3,
          writeSuccess156a4Trace2, writeSuccess156a4Trace1,
          writeSuccessTraceTail, a156a4. cbn. constructor.
      - exact Hx1.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits (Z_to_bv 64 0x156a4))
        (value := RVal_Bits writeSuccess156a4TargetMasked)
        (updated := RVal_Bits writeSuccess156a4TargetMasked).
      - reflexivity.
      - unfold writeSuccess156a4Trace11, writeSuccess156a4Trace10,
          writeSuccess156a4Trace9, writeSuccess156a4Trace8,
          writeSuccess156a4Trace7, writeSuccess156a4Trace6,
          writeSuccess156a4Trace5, writeSuccess156a4Trace4,
          writeSuccess156a4Trace3, writeSuccess156a4Trace2,
          writeSuccess156a4Trace1, writeSuccessTraceTail, a156a4. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a101d4) (trace := a101d4);
      try reflexivity; try constructor.
    exists (Z_to_bv 64 0x101d4). unfold writeSuccess156a4Regs.
    rewrite lookup_insert. destruct writeSuccess156a4ValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x101d4), a101d4.
    cbn. unfold writeSuccess156a4Regs. rewrite lookup_insert.
    destruct writeSuccess156a4ValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget Hnext. repeat split; reflexivity.
Qed.

Print Assumptions segment_156a4_mstatus.

Lemma segment_156a4 regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a4)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156a4Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d4 = Some a101d4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156a4Before regs global)
    (writeSuccess156a4Observations regs global)
    (writeSuccess156a4After regs global) /\
  (writeSuccess156a4After regs global).1.(seq_regs) = writeSuccess156a4Regs regs /\
  (writeSuccess156a4After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156a4Observations regs global)) = [].
Proof.
  exact (segment_156a4_mstatus regs global).
Qed.

Lemma writeSuccess156a4RegsLookupOther regs reg :
  reg <> "PC" -> reg <> "x1" ->
  writeSuccess156a4Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx1. unfold writeSuccess156a4Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence. reflexivity.
Qed.

Lemma writeSuccess156a4RegsDom regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a4)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156a4Ra) ->
  dom (writeSuccess156a4Regs regs) = dom regs.
Proof.
  intros Hpc Hx1. apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx1.
  unfold writeSuccess156a4Regs. rewrite !dom_insert_L. set_solver.
Qed.


Print Assumptions segment_156a4.
Print Assumptions writeSuccess156a4RegsLookupOther.
Print Assumptions writeSuccess156a4RegsDom.
