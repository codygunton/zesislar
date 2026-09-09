From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101e8.
Require Import IslaTraces.write_success_02.a101ec.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess101e8NextPc : bv 64 :=
  (Z_to_bv 64 0x101e8 + BV 64 4)%bv.
Definition writeSuccess101e8Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a101e8).
Definition writeSuccess101e8Trace2 := writeSuccessTraceTail writeSuccess101e8Trace1.
Definition writeSuccess101e8Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x101e8)) 3
    (writeSuccessTraceTail writeSuccess101e8Trace2).
Definition writeSuccess101e8Trace4 := writeSuccessTraceTail writeSuccess101e8Trace3.
Definition writeSuccess101e8Trace5 :=
  subst_trace (Val_Bits writeSuccess101e8NextPc) 4
    (writeSuccessTraceTail writeSuccess101e8Trace4).
Definition writeSuccess101e8Trace6 (left : bv 64) :=
  subst_trace (Val_Bits left) 5 (writeSuccessTraceTail writeSuccess101e8Trace5).
Definition writeSuccess101e8Trace7 left :=
  writeSuccessTraceTail (writeSuccess101e8Trace6 left).
Definition writeSuccess101e8Trace8 (left right : bv 64) :=
  subst_trace (Val_Bits right) 6
    (writeSuccessTraceTail (writeSuccess101e8Trace7 left)).
Definition writeSuccess101e8Trace9 left right :=
  writeSuccessTraceTail (writeSuccess101e8Trace8 left right).
Definition writeSuccess101e8Trace10 (left right : bv 64) :=
  subst_trace (Val_Bits (left + right)%bv) 7
    (writeSuccessTraceTail (writeSuccess101e8Trace9 left right)).
Definition writeSuccess101e8Trace11 left right :=
  writeSuccessTraceTail (writeSuccess101e8Trace10 left right).
Definition writeSuccess101e8Trace12 left right :=
  writeSuccessTraceTail (writeSuccess101e8Trace11 left right).

Definition writeSuccess101e8Regs regs (left right : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess101e8NextPc]>
    (<["x14" := RVal_Bits (left + right)%bv]> regs).
Definition writeSuccess101e8Before regs global : IslaState :=
  (writeSuccess15694Local a101e8 regs, global).
Definition writeSuccess101e8After regs global (left right : bv 64) : IslaState :=
  (writeSuccess15694Local a101ec
    (writeSuccess101e8Regs regs left right), global).

Lemma writeSuccess101e8NextPcExact :
  writeSuccess101e8NextPc = Z_to_bv 64 0x101ec.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Definition writeSuccess101e8Locals regs (left right : bv 64) :=
  [writeSuccess15694Local writeSuccess101e8Trace1 regs;
   writeSuccess15694Local writeSuccess101e8Trace2 regs;
   writeSuccess15694Local writeSuccess101e8Trace3 regs;
   writeSuccess15694Local writeSuccess101e8Trace4 regs;
   writeSuccess15694Local writeSuccess101e8Trace5 regs;
   writeSuccess15694Local (writeSuccess101e8Trace6 left) regs;
   writeSuccess15694Local (writeSuccess101e8Trace7 left) regs;
   writeSuccess15694Local (writeSuccess101e8Trace8 left right) regs;
   writeSuccess15694Local (writeSuccess101e8Trace9 left right) regs;
   writeSuccess15694Local (writeSuccess101e8Trace10 left right) regs;
   writeSuccess15694Local (writeSuccess101e8Trace11 left right)
     (<["x14" := RVal_Bits (left + right)%bv]> regs);
   writeSuccess15694Local (writeSuccess101e8Trace12 left right)
     (writeSuccess101e8Regs regs left right)].
Definition writeSuccess101e8PrefixObservations regs global
    (left right : bv 64) :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess101e8Locals regs left right).
Definition writeSuccess101e8Observations regs global (left right : bv 64) :=
  writeSuccess101e8PrefixObservations regs global left right ++
  [writeSuccess15694Observation
    (writeSuccess101e8After regs global left right).1 global].

Lemma writeSuccess101e8RegsLookupOther regs left right reg :
  reg <> "PC" -> reg <> "x14" ->
  writeSuccess101e8Regs regs left right !! reg = regs !! reg.
Proof. intros Hpc Hdest. unfold writeSuccess101e8Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence. reflexivity. Qed.

Lemma writeSuccess101e8RegsDom regs left right oldX14 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e8)) ->
  regs !! "x14" = Some oldX14 ->
  dom (writeSuccess101e8Regs regs left right) = dom regs.
Proof. intros Hpc Hdest. apply elem_of_dom_2 in Hpc.
  apply elem_of_dom_2 in Hdest. unfold writeSuccess101e8Regs.
  rewrite !dom_insert_L. set_solver. Qed.

Lemma writeSuccess101e8PrefixPath regs global (left right : bv 64) oldX14 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e8)) ->
  regs !! "x10" = Some (RVal_Bits left) ->
  regs !! "x15" = Some (RVal_Bits right) ->
  regs !! "x14" = Some oldX14 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionPrefixPath (writeSuccess101e8Before regs global)
    (writeSuccess101e8PrefixObservations regs global left right)
    (writeSuccess15694Local tnil
      (writeSuccess101e8Regs regs left right), global).
Proof.
  intros Hpc Hleft Hright Hdest Hmstatus.
  unfold writeSuccess101e8PrefixObservations, writeSuccess101e8Locals.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess101e8Before,
      writeSuccess101e8Trace1, writeSuccessTraceTail, a101e8. cbn.
    apply DeclareConstBitVecS' with (b := BV 64 0). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess101e8Trace1,
      writeSuccessTraceTail, a101e8. cbn. eapply AssumeS. exact Hmstatus. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess101e8Trace2, writeSuccess101e8Trace1,
      writeSuccessTraceTail, a101e8. cbn.
    apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x101e8). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with
      (root := RVal_Bits (Z_to_bv 64 0x101e8))
      (value := RVal_Bits (Z_to_bv 64 0x101e8)).
    - reflexivity.
    - unfold writeSuccess101e8Trace3, writeSuccess101e8Trace2,
        writeSuccess101e8Trace1, writeSuccessTraceTail, a101e8. cbn. constructor.
    - exact Hpc. - reflexivity. - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101e8Trace4 writeSuccess101e8Trace3
      writeSuccess101e8Trace2 writeSuccess101e8Trace1
      writeSuccess101e8NextPc writeSuccessTraceTail a101e8].
    eapply DefineConstS with (v := Val_Bits writeSuccess101e8NextPc). reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity. cbn [writeSuccess101e8Trace5
      writeSuccess101e8Trace4 writeSuccess101e8Trace3 writeSuccess101e8Trace2
      writeSuccess101e8Trace1 writeSuccess101e8NextPc writeSuccessTraceTail a101e8].
    apply DeclareConstBitVecS' with (b := left). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with (root := RVal_Bits left)
      (value := RVal_Bits left).
    - reflexivity.
    - cbn [writeSuccess101e8Trace6 writeSuccess101e8Trace5
        writeSuccess101e8Trace4 writeSuccess101e8Trace3
        writeSuccess101e8Trace2 writeSuccess101e8Trace1
        writeSuccess101e8NextPc writeSuccessTraceTail a101e8]. constructor.
    - exact Hleft. - reflexivity. - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101e8Trace7 writeSuccess101e8Trace6
      writeSuccess101e8Trace5 writeSuccess101e8Trace4
      writeSuccess101e8Trace3 writeSuccess101e8Trace2
      writeSuccess101e8Trace1 writeSuccess101e8NextPc
      writeSuccessTraceTail a101e8].
    apply DeclareConstBitVecS' with (b := right). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with (root := RVal_Bits right)
      (value := RVal_Bits right).
    - reflexivity.
    - cbn [writeSuccess101e8Trace8 writeSuccess101e8Trace7
        writeSuccess101e8Trace6 writeSuccess101e8Trace5
        writeSuccess101e8Trace4 writeSuccess101e8Trace3
        writeSuccess101e8Trace2 writeSuccess101e8Trace1
        writeSuccess101e8NextPc writeSuccessTraceTail a101e8]. constructor.
    - exact Hright. - reflexivity. - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101e8Trace9 writeSuccess101e8Trace8
      writeSuccess101e8Trace7 writeSuccess101e8Trace6
      writeSuccess101e8Trace5 writeSuccess101e8Trace4
      writeSuccess101e8Trace3 writeSuccess101e8Trace2
      writeSuccess101e8Trace1 writeSuccess101e8NextPc
      writeSuccessTraceTail a101e8].
    eapply DefineConstS with (v := Val_Bits (left + right)%bv). reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqWriteReg with (root := oldX14)
      (value := RVal_Bits (left + right)%bv)
      (updated := RVal_Bits (left + right)%bv).
    - reflexivity.
    - cbn [writeSuccess101e8Trace10 writeSuccess101e8Trace9
        writeSuccess101e8Trace8 writeSuccess101e8Trace7
        writeSuccess101e8Trace6 writeSuccess101e8Trace5
        writeSuccess101e8Trace4 writeSuccess101e8Trace3
        writeSuccess101e8Trace2 writeSuccess101e8Trace1
        writeSuccess101e8NextPc writeSuccessTraceTail a101e8]. constructor.
    - exact Hdest. - reflexivity. - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqWriteReg with
      (root := RVal_Bits (Z_to_bv 64 0x101e8))
      (value := RVal_Bits writeSuccess101e8NextPc)
      (updated := RVal_Bits writeSuccess101e8NextPc).
    - reflexivity.
    - cbn [writeSuccess101e8Trace11 writeSuccess101e8Trace10
        writeSuccess101e8Trace9 writeSuccess101e8Trace8
        writeSuccess101e8Trace7 writeSuccess101e8Trace6
        writeSuccess101e8Trace5 writeSuccess101e8Trace4
        writeSuccess101e8Trace3 writeSuccess101e8Trace2
        writeSuccess101e8Trace1 writeSuccess101e8NextPc
        writeSuccessTraceTail a101e8]. constructor.
    - rewrite lookup_insert_ne; last done. exact Hpc.
    - reflexivity. - reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Lemma segment_101e8_mstatus regs global (left right : bv 64) oldX14 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e8)) ->
  regs !! "x10" = Some (RVal_Bits left) ->
  regs !! "x15" = Some (RVal_Bits right) ->
  regs !! "x14" = Some oldX14 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e8 = Some a101e8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101e8Before regs global)
    (writeSuccess101e8Observations regs global left right)
    (writeSuccess101e8After regs global left right) /\
  (writeSuccess101e8After regs global left right).1.(seq_regs) =
    writeSuccess101e8Regs regs left right /\
  (writeSuccess101e8After regs global left right).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels
    (writeSuccess101e8Observations regs global left right)) = [].
Proof.
  intros Hpc Hleft Hright Hdest Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess101e8Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil
      (writeSuccess101e8Regs regs left right), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x101e8), a101e8.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - eapply writeSuccess101e8PrefixPath; eauto.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a101ec) (trace := a101ec).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x101ec). unfold writeSuccess101e8Regs.
      rewrite lookup_insert. rewrite writeSuccess101e8NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x101ec), a101ec.
    cbn. unfold writeSuccess101e8Regs. rewrite lookup_insert.
    rewrite writeSuccess101e8NextPcExact Hnext. repeat split; reflexivity.
Qed.

Lemma segment_101e8 regs global (left right : bv 64) oldX14 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e8)) ->
  regs !! "x10" = Some (RVal_Bits left) ->
  regs !! "x15" = Some (RVal_Bits right) ->
  regs !! "x14" = Some oldX14 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e8 = Some a101e8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101e8Before regs global)
    (writeSuccess101e8Observations regs global left right)
    (writeSuccess101e8After regs global left right) /\
  (writeSuccess101e8After regs global left right).1.(seq_regs) =
    writeSuccess101e8Regs regs left right /\
  (writeSuccess101e8After regs global left right).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels
    (writeSuccess101e8Observations regs global left right)) = [].
Proof.
  intros Hpc Hleft Hright Hdest Hcode Hnext Hmstatus.
  eapply segment_101e8_mstatus; eauto.
Qed.

Print Assumptions writeSuccess101e8PrefixPath.
Print Assumptions segment_101e8_mstatus.
Print Assumptions segment_101e8.
Print Assumptions writeSuccess101e8RegsLookupOther.
Print Assumptions writeSuccess101e8RegsDom.
