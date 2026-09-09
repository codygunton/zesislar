From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_93.a156cc.
Require Import IslaTraces.write_success_01.a10190.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156ccAlignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x1" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 0xfffffffffffffac8)) Mk_annot]
        Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Definition writeSuccess156ccRa : bv 64 := writeSuccess156c8Link.
Definition writeSuccess156ccLink : bv 64 :=
  (Z_to_bv 64 0x156cc + BV 64 4)%bv.
Definition writeSuccess156ccTarget : bv 64 :=
  (writeSuccess156ccRa + BV 64 0xfffffffffffffac8)%bv.
Definition writeSuccess156ccTargetMasked : bv 64 :=
  bv_or (bv_and writeSuccess156ccTarget (BV 64 0xfffffffffffffffe))
    (BV 64 0).
Definition writeSuccess156ccTargetBit : bv 1 :=
  bv_extract 0 1
    (bv_shiftr writeSuccess156ccTargetMasked (BV 64 1)).

Definition writeSuccess156ccTrace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156cc).
Definition writeSuccess156ccTrace2 := writeSuccessTraceTail writeSuccess156ccTrace1.
Definition writeSuccess156ccTrace3 :=
  subst_trace (Val_Bits writeSuccess156ccRa) 3
    (writeSuccessTraceTail writeSuccess156ccTrace2).
Definition writeSuccess156ccTrace4 := writeSuccessTraceTail writeSuccess156ccTrace3.
Definition writeSuccess156ccTrace5 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156cc)) 4
    (writeSuccessTraceTail writeSuccess156ccTrace4).
Definition writeSuccess156ccTrace6 := writeSuccessTraceTail writeSuccess156ccTrace5.
Definition writeSuccess156ccTrace7 :=
  subst_trace (Val_Bits writeSuccess156ccLink) 5
    (writeSuccessTraceTail writeSuccess156ccTrace6).
Definition writeSuccess156ccTrace8 := writeSuccessTraceTail writeSuccess156ccTrace7.
Definition writeSuccess156ccTrace9 :=
  subst_trace (Val_Bits writeSuccess156ccTargetMasked) 7
    (writeSuccessTraceTail writeSuccess156ccTrace8).
Definition writeSuccess156ccTrace10 :=
  subst_trace (Val_Bits writeSuccess156ccTargetBit) 8
    (writeSuccessTraceTail writeSuccess156ccTrace9).
Definition writeSuccess156ccTrace11 := writeSuccessTraceTail writeSuccess156ccTrace10.
Definition writeSuccess156ccTrace12 := writeSuccessTraceTail writeSuccess156ccTrace11.

Definition writeSuccess156ccRegs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156ccTargetMasked]>
    (<["x1" := RVal_Bits writeSuccess156ccLink]> regs).
Definition writeSuccess156ccBefore regs global : IslaState :=
  (writeSuccess15694Local a156cc regs, global).
Definition writeSuccess156ccAfter regs global : IslaState :=
  (writeSuccess15694Local a10190 (writeSuccess156ccRegs regs), global).

Lemma writeSuccess156ccValuesExact :
  writeSuccess156ccRa = Z_to_bv 64 0x106c8 /\
  writeSuccess156ccLink = Z_to_bv 64 0x156d0 /\
  writeSuccess156ccTarget = Z_to_bv 64 0x10190 /\
  writeSuccess156ccTargetMasked = Z_to_bv 64 0x10190.
Proof.
  vm_compute. repeat split; apply bv_eq; reflexivity.
Qed.

Lemma writeSuccess156ccAlignmentHolds regs :
  regs !! "x1" = Some (RVal_Bits writeSuccess156ccRa) ->
  eval_a_exp regs writeSuccess156ccAlignment = Some (Val_Bool true).
Proof.
  intros Hx1. unfold writeSuccess156ccAlignment. cbn. rewrite Hx1. cbn.
  unfold writeSuccess156ccRa, writeSuccess156c8Link. vm_compute.
  reflexivity.
Qed.

Definition writeSuccess156ccLocals regs : list seq_local_state :=
  [writeSuccess15694Local writeSuccess156ccTrace1 regs;
   writeSuccess15694Local writeSuccess156ccTrace2 regs;
   writeSuccess15694Local writeSuccess156ccTrace3 regs;
   writeSuccess15694Local writeSuccess156ccTrace4 regs;
   writeSuccess15694Local writeSuccess156ccTrace5 regs;
   writeSuccess15694Local writeSuccess156ccTrace6 regs;
   writeSuccess15694Local writeSuccess156ccTrace7 regs;
   writeSuccess15694Local writeSuccess156ccTrace8 regs;
   writeSuccess15694Local writeSuccess156ccTrace9 regs;
   writeSuccess15694Local writeSuccess156ccTrace10 regs;
   writeSuccess15694Local writeSuccess156ccTrace11
     (<["x1" := RVal_Bits writeSuccess156ccLink]> regs);
   writeSuccess15694Local writeSuccess156ccTrace12
     (writeSuccess156ccRegs regs)].
Definition writeSuccess156ccPrefixObservations regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess156ccLocals regs).
Definition writeSuccess156ccObservations regs global :=
  writeSuccess156ccPrefixObservations regs global ++
  [writeSuccess15694Observation (writeSuccess156ccAfter regs global).1 global].

Definition writeSuccess156ccPrefix8Observations regs global :
    list IslaMicroObservation :=
  map (fun local => {| microLabels := []; microAfter := (local, global) |})
    (firstn 8 (writeSuccess156ccLocals regs)).

Definition writeSuccess156ccTailObservations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156ccTrace9 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156ccTrace10 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156ccTrace11
       (<["x1" := RVal_Bits writeSuccess156ccLink]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156ccTrace12
       (writeSuccess156ccRegs regs)) global;
   writeSuccess15694Observation (writeSuccess156ccAfter regs global).1 global].

Definition writeSuccess156ccTailFirst2Observations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156ccTrace9 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156ccTrace10 regs) global].

Definition writeSuccess156ccTailLastObservations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156ccTrace11
       (<["x1" := RVal_Bits writeSuccess156ccLink]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156ccTrace12
       (writeSuccess156ccRegs regs)) global;
   writeSuccess15694Observation (writeSuccess156ccAfter regs global).1 global].

Lemma writeSuccess156ccTailObservationsSplit regs global :
  writeSuccess156ccTailObservations regs global =
    writeSuccess156ccTailFirst2Observations regs global ++
    writeSuccess156ccTailLastObservations regs global.
Proof. reflexivity. Qed.

Lemma writeSuccess156ccObservationsSplit regs global :
  writeSuccess156ccObservations regs global =
    writeSuccess156ccPrefix8Observations regs global ++
    writeSuccess156ccTailObservations regs global.
Proof. reflexivity. Qed.

Lemma segment_156cc_mstatus regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156cc)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156ccRa) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156cc = Some a156cc ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156ccBefore regs global)
    (writeSuccess156ccObservations regs global)
    (writeSuccess156ccAfter regs global) /\
  (writeSuccess156ccAfter regs global).1.(seq_regs) = writeSuccess156ccRegs regs /\
  (writeSuccess156ccAfter regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156ccObservations regs global)) = [].
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus.
  have Halign := writeSuccess156ccAlignmentHolds regs Hx1.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156ccObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156ccRegs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156cc), a156cc.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156ccPrefixObservations, writeSuccess156ccLocals. cbn.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156ccBefore,
        writeSuccess156ccTrace1, writeSuccessTraceTail, a156cc. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess156ccTrace1,
        writeSuccessTraceTail, a156cc. cbn. apply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156ccTrace2,
        writeSuccess156ccTrace1, writeSuccessTraceTail, a156cc. cbn.
      apply DeclareConstBitVecS' with (b := writeSuccess156ccRa). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess156ccTrace3,
        writeSuccess156ccTrace2, writeSuccess156ccTrace1,
        writeSuccessTraceTail, a156cc. cbn. apply AssumeS. exact Halign. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156ccTrace4,
        writeSuccess156ccTrace3, writeSuccess156ccTrace2,
        writeSuccess156ccTrace1, writeSuccessTraceTail, a156cc. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156cc). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits (Z_to_bv 64 0x156cc))
        (value := RVal_Bits (Z_to_bv 64 0x156cc)).
      - reflexivity.
      - unfold writeSuccess156ccTrace5, writeSuccess156ccTrace4,
          writeSuccess156ccTrace3, writeSuccess156ccTrace2,
          writeSuccess156ccTrace1, writeSuccessTraceTail, a156cc. cbn. constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156ccTrace6,
        writeSuccess156ccTrace5, writeSuccess156ccTrace4,
        writeSuccess156ccTrace3, writeSuccess156ccTrace2,
        writeSuccess156ccTrace1, writeSuccess156ccLink,
        writeSuccessTraceTail, a156cc. cbn.
      eapply DefineConstS with (v := Val_Bits (Z_to_bv 64 0x156cc + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits writeSuccess156ccRa)
        (value := RVal_Bits writeSuccess156ccRa).
      - reflexivity.
      - unfold writeSuccess156ccTrace7, writeSuccess156ccTrace6,
          writeSuccess156ccTrace5, writeSuccess156ccTrace4,
          writeSuccess156ccTrace3, writeSuccess156ccTrace2,
          writeSuccess156ccTrace1, writeSuccessTraceTail, a156cc. cbn. constructor.
      - exact Hx1.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156ccTrace8,
        writeSuccess156ccTrace7, writeSuccess156ccTrace6,
        writeSuccess156ccTrace5, writeSuccess156ccTrace4,
        writeSuccess156ccTrace3, writeSuccess156ccTrace2,
        writeSuccess156ccTrace1, writeSuccess156ccTargetMasked,
        writeSuccess156ccTarget, writeSuccessTraceTail, a156cc. cbn.
      eapply DefineConstS with
        (v := Val_Bits writeSuccess156ccTargetMasked).
      unfold writeSuccess156ccTargetMasked, writeSuccess156ccTarget.
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156ccTrace9,
        writeSuccess156ccTrace8, writeSuccess156ccTrace7,
        writeSuccess156ccTrace6, writeSuccess156ccTrace5,
        writeSuccess156ccTrace4, writeSuccess156ccTrace3,
        writeSuccess156ccTrace2, writeSuccess156ccTrace1,
        writeSuccess156ccTargetBit, writeSuccessTraceTail, a156cc. cbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess156ccTargetBit).
      unfold writeSuccess156ccTargetBit, writeSuccess156ccTargetMasked,
        writeSuccess156ccTarget. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits writeSuccess156ccRa)
        (value := RVal_Bits writeSuccess156ccLink)
        (updated := RVal_Bits writeSuccess156ccLink).
      - reflexivity.
      - unfold writeSuccess156ccTrace10, writeSuccess156ccTrace9,
          writeSuccess156ccTrace8, writeSuccess156ccTrace7,
          writeSuccess156ccTrace6, writeSuccess156ccTrace5,
          writeSuccess156ccTrace4, writeSuccess156ccTrace3,
          writeSuccess156ccTrace2, writeSuccess156ccTrace1,
          writeSuccessTraceTail, a156cc. cbn. constructor.
      - exact Hx1.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits (Z_to_bv 64 0x156cc))
        (value := RVal_Bits writeSuccess156ccTargetMasked)
        (updated := RVal_Bits writeSuccess156ccTargetMasked).
      - reflexivity.
      - unfold writeSuccess156ccTrace11, writeSuccess156ccTrace10,
          writeSuccess156ccTrace9, writeSuccess156ccTrace8,
          writeSuccess156ccTrace7, writeSuccess156ccTrace6,
          writeSuccess156ccTrace5, writeSuccess156ccTrace4,
          writeSuccess156ccTrace3, writeSuccess156ccTrace2,
          writeSuccess156ccTrace1, writeSuccessTraceTail, a156cc. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a10190) (trace := a10190);
      try reflexivity; try constructor.
    exists (Z_to_bv 64 0x10190). unfold writeSuccess156ccRegs.
    rewrite lookup_insert. destruct writeSuccess156ccValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x10190), a10190.
    cbn. unfold writeSuccess156ccRegs. rewrite lookup_insert.
    destruct writeSuccess156ccValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget Hnext. repeat split; reflexivity.
Qed.

Print Assumptions segment_156cc_mstatus.

Lemma segment_156cc regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156cc)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156ccRa) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156cc = Some a156cc ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156ccBefore regs global)
    (writeSuccess156ccObservations regs global)
    (writeSuccess156ccAfter regs global) /\
  (writeSuccess156ccAfter regs global).1.(seq_regs) = writeSuccess156ccRegs regs /\
  (writeSuccess156ccAfter regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156ccObservations regs global)) = [].
Proof.
  exact (segment_156cc_mstatus regs global).
Qed.

Lemma writeSuccess156ccRegsLookupOther regs reg :
  reg <> "PC" -> reg <> "x1" ->
  writeSuccess156ccRegs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx1. unfold writeSuccess156ccRegs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence. reflexivity.
Qed.

Lemma writeSuccess156ccRegsDom regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156cc)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156ccRa) ->
  dom (writeSuccess156ccRegs regs) = dom regs.
Proof.
  intros Hpc Hx1. apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx1.
  unfold writeSuccess156ccRegs. rewrite !dom_insert_L. set_solver.
Qed.


Print Assumptions segment_156cc.
Print Assumptions writeSuccess156ccRegsLookupOther.
Print Assumptions writeSuccess156ccRegsDom.
