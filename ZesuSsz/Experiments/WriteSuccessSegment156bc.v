From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_92.a156bc.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156bcAlignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x1" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 0x658)) Mk_annot]
        Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Definition writeSuccess156bcRa : bv 64 := writeSuccess156b8Link.
Definition writeSuccess156bcLink : bv 64 :=
  (Z_to_bv 64 0x156bc + BV 64 4)%bv.
Definition writeSuccess156bcTarget : bv 64 :=
  (writeSuccess156bcRa + BV 64 0x658)%bv.
Definition writeSuccess156bcTargetMasked : bv 64 :=
  bv_or (bv_and writeSuccess156bcTarget (BV 64 0xfffffffffffffffe))
    (BV 64 0).
Definition writeSuccess156bcTargetBit : bv 1 :=
  bv_extract 0 1
    (bv_shiftr writeSuccess156bcTargetMasked (BV 64 1)).

Definition writeSuccess156bcTrace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156bc).
Definition writeSuccess156bcTrace2 := writeSuccessTraceTail writeSuccess156bcTrace1.
Definition writeSuccess156bcTrace3 :=
  subst_trace (Val_Bits writeSuccess156bcRa) 3
    (writeSuccessTraceTail writeSuccess156bcTrace2).
Definition writeSuccess156bcTrace4 := writeSuccessTraceTail writeSuccess156bcTrace3.
Definition writeSuccess156bcTrace5 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156bc)) 4
    (writeSuccessTraceTail writeSuccess156bcTrace4).
Definition writeSuccess156bcTrace6 := writeSuccessTraceTail writeSuccess156bcTrace5.
Definition writeSuccess156bcTrace7 :=
  subst_trace (Val_Bits writeSuccess156bcLink) 5
    (writeSuccessTraceTail writeSuccess156bcTrace6).
Definition writeSuccess156bcTrace8 := writeSuccessTraceTail writeSuccess156bcTrace7.
Definition writeSuccess156bcTrace9 :=
  subst_trace (Val_Bits writeSuccess156bcTargetMasked) 7
    (writeSuccessTraceTail writeSuccess156bcTrace8).
Definition writeSuccess156bcTrace10 :=
  subst_trace (Val_Bits writeSuccess156bcTargetBit) 8
    (writeSuccessTraceTail writeSuccess156bcTrace9).
Definition writeSuccess156bcTrace11 := writeSuccessTraceTail writeSuccess156bcTrace10.
Definition writeSuccess156bcTrace12 := writeSuccessTraceTail writeSuccess156bcTrace11.

Definition writeSuccess156bcRegs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156bcTargetMasked]>
    (<["x1" := RVal_Bits writeSuccess156bcLink]> regs).
Definition writeSuccess156bcBefore regs global : IslaState :=
  (writeSuccess15694Local a156bc regs, global).
Definition writeSuccess156bcAfter regs global : IslaState :=
  (writeSuccess15694Local a15d10 (writeSuccess156bcRegs regs), global).

Lemma writeSuccess156bcValuesExact :
  writeSuccess156bcRa = Z_to_bv 64 0x156b8 /\
  writeSuccess156bcLink = Z_to_bv 64 0x156c0 /\
  writeSuccess156bcTarget = Z_to_bv 64 0x15d10 /\
  writeSuccess156bcTargetMasked = Z_to_bv 64 0x15d10.
Proof.
  vm_compute. repeat split; apply bv_eq; reflexivity.
Qed.

Lemma writeSuccess156bcAlignmentHolds regs :
  regs !! "x1" = Some (RVal_Bits writeSuccess156bcRa) ->
  eval_a_exp regs writeSuccess156bcAlignment = Some (Val_Bool true).
Proof.
  intros Hx1. unfold writeSuccess156bcAlignment. cbn. rewrite Hx1. cbn.
  unfold writeSuccess156bcRa, writeSuccess156b8Link. vm_compute.
  reflexivity.
Qed.

Definition writeSuccess156bcLocals regs : list seq_local_state :=
  [writeSuccess15694Local writeSuccess156bcTrace1 regs;
   writeSuccess15694Local writeSuccess156bcTrace2 regs;
   writeSuccess15694Local writeSuccess156bcTrace3 regs;
   writeSuccess15694Local writeSuccess156bcTrace4 regs;
   writeSuccess15694Local writeSuccess156bcTrace5 regs;
   writeSuccess15694Local writeSuccess156bcTrace6 regs;
   writeSuccess15694Local writeSuccess156bcTrace7 regs;
   writeSuccess15694Local writeSuccess156bcTrace8 regs;
   writeSuccess15694Local writeSuccess156bcTrace9 regs;
   writeSuccess15694Local writeSuccess156bcTrace10 regs;
   writeSuccess15694Local writeSuccess156bcTrace11
     (<["x1" := RVal_Bits writeSuccess156bcLink]> regs);
   writeSuccess15694Local writeSuccess156bcTrace12
     (writeSuccess156bcRegs regs)].
Definition writeSuccess156bcPrefixObservations regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess156bcLocals regs).
Definition writeSuccess156bcObservations regs global :=
  writeSuccess156bcPrefixObservations regs global ++
  [writeSuccess15694Observation (writeSuccess156bcAfter regs global).1 global].

Definition writeSuccess156bcPrefix8Observations regs global :
    list IslaMicroObservation :=
  map (fun local => {| microLabels := []; microAfter := (local, global) |})
    (firstn 8 (writeSuccess156bcLocals regs)).

Definition writeSuccess156bcTailObservations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156bcTrace9 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156bcTrace10 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156bcTrace11
       (<["x1" := RVal_Bits writeSuccess156bcLink]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156bcTrace12
       (writeSuccess156bcRegs regs)) global;
   writeSuccess15694Observation (writeSuccess156bcAfter regs global).1 global].

Definition writeSuccess156bcTailFirst2Observations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156bcTrace9 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156bcTrace10 regs) global].

Definition writeSuccess156bcTailLastObservations regs global :
    list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156bcTrace11
       (<["x1" := RVal_Bits writeSuccess156bcLink]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156bcTrace12
       (writeSuccess156bcRegs regs)) global;
   writeSuccess15694Observation (writeSuccess156bcAfter regs global).1 global].

Lemma writeSuccess156bcTailObservationsSplit regs global :
  writeSuccess156bcTailObservations regs global =
    writeSuccess156bcTailFirst2Observations regs global ++
    writeSuccess156bcTailLastObservations regs global.
Proof. reflexivity. Qed.

Lemma writeSuccess156bcObservationsSplit regs global :
  writeSuccess156bcObservations regs global =
    writeSuccess156bcPrefix8Observations regs global ++
    writeSuccess156bcTailObservations regs global.
Proof. reflexivity. Qed.

Lemma segment_156bc_mstatus regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156bc)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156bcRa) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156bc = Some a156bc ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156bcBefore regs global)
    (writeSuccess156bcObservations regs global)
    (writeSuccess156bcAfter regs global) /\
  (writeSuccess156bcAfter regs global).1.(seq_regs) = writeSuccess156bcRegs regs /\
  (writeSuccess156bcAfter regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156bcObservations regs global)) = [].
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus.
  have Halign := writeSuccess156bcAlignmentHolds regs Hx1.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156bcObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156bcRegs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156bc), a156bc.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156bcPrefixObservations, writeSuccess156bcLocals. cbn.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156bcBefore,
        writeSuccess156bcTrace1, writeSuccessTraceTail, a156bc. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess156bcTrace1,
        writeSuccessTraceTail, a156bc. cbn. apply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156bcTrace2,
        writeSuccess156bcTrace1, writeSuccessTraceTail, a156bc. cbn.
      apply DeclareConstBitVecS' with (b := writeSuccess156bcRa). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess156bcTrace3,
        writeSuccess156bcTrace2, writeSuccess156bcTrace1,
        writeSuccessTraceTail, a156bc. cbn. apply AssumeS. exact Halign. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156bcTrace4,
        writeSuccess156bcTrace3, writeSuccess156bcTrace2,
        writeSuccess156bcTrace1, writeSuccessTraceTail, a156bc. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156bc). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits (Z_to_bv 64 0x156bc))
        (value := RVal_Bits (Z_to_bv 64 0x156bc)).
      - reflexivity.
      - unfold writeSuccess156bcTrace5, writeSuccess156bcTrace4,
          writeSuccess156bcTrace3, writeSuccess156bcTrace2,
          writeSuccess156bcTrace1, writeSuccessTraceTail, a156bc. cbn. constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156bcTrace6,
        writeSuccess156bcTrace5, writeSuccess156bcTrace4,
        writeSuccess156bcTrace3, writeSuccess156bcTrace2,
        writeSuccess156bcTrace1, writeSuccess156bcLink,
        writeSuccessTraceTail, a156bc. cbn.
      eapply DefineConstS with (v := Val_Bits (Z_to_bv 64 0x156bc + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits writeSuccess156bcRa)
        (value := RVal_Bits writeSuccess156bcRa).
      - reflexivity.
      - unfold writeSuccess156bcTrace7, writeSuccess156bcTrace6,
          writeSuccess156bcTrace5, writeSuccess156bcTrace4,
          writeSuccess156bcTrace3, writeSuccess156bcTrace2,
          writeSuccess156bcTrace1, writeSuccessTraceTail, a156bc. cbn. constructor.
      - exact Hx1.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156bcTrace8,
        writeSuccess156bcTrace7, writeSuccess156bcTrace6,
        writeSuccess156bcTrace5, writeSuccess156bcTrace4,
        writeSuccess156bcTrace3, writeSuccess156bcTrace2,
        writeSuccess156bcTrace1, writeSuccess156bcTargetMasked,
        writeSuccess156bcTarget, writeSuccessTraceTail, a156bc. cbn.
      eapply DefineConstS with
        (v := Val_Bits writeSuccess156bcTargetMasked).
      unfold writeSuccess156bcTargetMasked, writeSuccess156bcTarget.
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess156bcTrace9,
        writeSuccess156bcTrace8, writeSuccess156bcTrace7,
        writeSuccess156bcTrace6, writeSuccess156bcTrace5,
        writeSuccess156bcTrace4, writeSuccess156bcTrace3,
        writeSuccess156bcTrace2, writeSuccess156bcTrace1,
        writeSuccess156bcTargetBit, writeSuccessTraceTail, a156bc. cbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess156bcTargetBit).
      unfold writeSuccess156bcTargetBit, writeSuccess156bcTargetMasked,
        writeSuccess156bcTarget. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits writeSuccess156bcRa)
        (value := RVal_Bits writeSuccess156bcLink)
        (updated := RVal_Bits writeSuccess156bcLink).
      - reflexivity.
      - unfold writeSuccess156bcTrace10, writeSuccess156bcTrace9,
          writeSuccess156bcTrace8, writeSuccess156bcTrace7,
          writeSuccess156bcTrace6, writeSuccess156bcTrace5,
          writeSuccess156bcTrace4, writeSuccess156bcTrace3,
          writeSuccess156bcTrace2, writeSuccess156bcTrace1,
          writeSuccessTraceTail, a156bc. cbn. constructor.
      - exact Hx1.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits (Z_to_bv 64 0x156bc))
        (value := RVal_Bits writeSuccess156bcTargetMasked)
        (updated := RVal_Bits writeSuccess156bcTargetMasked).
      - reflexivity.
      - unfold writeSuccess156bcTrace11, writeSuccess156bcTrace10,
          writeSuccess156bcTrace9, writeSuccess156bcTrace8,
          writeSuccess156bcTrace7, writeSuccess156bcTrace6,
          writeSuccess156bcTrace5, writeSuccess156bcTrace4,
          writeSuccess156bcTrace3, writeSuccess156bcTrace2,
          writeSuccess156bcTrace1, writeSuccessTraceTail, a156bc. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15d10) (trace := a15d10);
      try reflexivity; try constructor.
    exists (Z_to_bv 64 0x15d10). unfold writeSuccess156bcRegs.
    rewrite lookup_insert. destruct writeSuccess156bcValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15d10), a15d10.
    cbn. unfold writeSuccess156bcRegs. rewrite lookup_insert.
    destruct writeSuccess156bcValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget Hnext. repeat split; reflexivity.
Qed.

Print Assumptions segment_156bc_mstatus.

Lemma segment_156bc regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156bc)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156bcRa) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156bc = Some a156bc ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156bcBefore regs global)
    (writeSuccess156bcObservations regs global)
    (writeSuccess156bcAfter regs global) /\
  (writeSuccess156bcAfter regs global).1.(seq_regs) = writeSuccess156bcRegs regs /\
  (writeSuccess156bcAfter regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156bcObservations regs global)) = [].
Proof.
  exact (segment_156bc_mstatus regs global).
Qed.

Lemma writeSuccess156bcRegsLookupOther regs reg :
  reg <> "PC" -> reg <> "x1" ->
  writeSuccess156bcRegs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx1. unfold writeSuccess156bcRegs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence. reflexivity.
Qed.

Lemma writeSuccess156bcRegsDom regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156bc)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156bcRa) ->
  dom (writeSuccess156bcRegs regs) = dom regs.
Proof.
  intros Hpc Hx1. apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx1.
  unfold writeSuccess156bcRegs. rewrite !dom_insert_L. set_solver.
Qed.


Print Assumptions segment_156bc.
Print Assumptions writeSuccess156bcRegsLookupOther.
Print Assumptions writeSuccess156bcRegsDom.
