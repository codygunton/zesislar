From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d20.
Require Import IslaTraces.write_success_07.a15d24.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess15d20Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a15d20).
Definition writeSuccess15d20Trace2 := writeSuccessTraceTail writeSuccess15d20Trace1.
Definition writeSuccess15d20Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15d20)) 3
    (writeSuccessTraceTail writeSuccess15d20Trace2).
Definition writeSuccess15d20Trace4 := writeSuccessTraceTail writeSuccess15d20Trace3.
Definition writeSuccess15d20NextPc : bv 64 :=
  (Z_to_bv 64 0x15d20 + BV 64 4)%bv.
Definition writeSuccess15d20Trace5 :=
  subst_trace (Val_Bits writeSuccess15d20NextPc) 4
    (writeSuccessTraceTail writeSuccess15d20Trace4).
Definition writeSuccess15d20Trace6 := writeSuccessTraceTail writeSuccess15d20Trace5.
Definition writeSuccess15d20Trace7 := writeSuccessTraceTail writeSuccess15d20Trace6.

Definition writeSuccess15d20Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess15d20NextPc]>
    (<["x11" := RVal_Bits (BV 64 8)]> regs).

Lemma writeSuccess15d20RegsLookupOther regs reg :
  reg <> "PC" ->
  reg <> "x11" ->
  writeSuccess15d20Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx12. unfold writeSuccess15d20Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Lemma writeSuccess15d20RegsDom regs oldX11 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d20)) ->
  regs !! "x11" = Some oldX11 ->
  dom (writeSuccess15d20Regs regs) = dom regs.
Proof.
  intros Hpc Hx12.
  apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx12.
  unfold writeSuccess15d20Regs. rewrite !dom_insert_L.
  set_solver.
Qed.

Definition writeSuccess15d20Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a15d20 regs, global).

Definition writeSuccess15d20After (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a15d24 (writeSuccess15d20Regs regs), global).

Lemma writeSuccess15d20NextPcExact :
  writeSuccess15d20NextPc = Z_to_bv 64 0x15d24.
Proof. unfold writeSuccess15d20NextPc. bv_solve. Qed.

Definition writeSuccess15d20PrefixObservations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d20Trace1 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d20Trace2 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d20Trace3 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d20Trace4 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d20Trace5 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d20Trace6
       (<["x11" := RVal_Bits (BV 64 8)]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15d20Trace7
       (writeSuccess15d20Regs regs)) global].

Definition writeSuccess15d20Observations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  writeSuccess15d20PrefixObservations regs global ++
  [writeSuccess15694Observation
     (writeSuccess15d20After regs global).1 global].

Lemma segment_15d20_mstatus (regs : reg_map) (global : seq_global_state) oldX11 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d20)) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d20Before regs global)
    (writeSuccess15d20Observations regs global)
    (writeSuccess15d20After regs global) /\
  (writeSuccess15d20After regs global).1.(seq_regs) =
    writeSuccess15d20Regs regs /\
  (writeSuccess15d20After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15d20Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess15d20Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess15d20Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15d20), a15d20.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess15d20PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d20Before, writeSuccess15d20Trace1,
        writeSuccessTraceTail, a15d20. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess15d20Trace1, writeSuccessTraceTail, a15d20. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d20Trace2, writeSuccess15d20Trace1,
        writeSuccessTraceTail, a15d20. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15d20). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d20))
        (value := RVal_Bits (Z_to_bv 64 0x15d20)).
      - reflexivity.
      - unfold writeSuccess15d20Trace3, writeSuccess15d20Trace2,
          writeSuccess15d20Trace1, writeSuccessTraceTail, a15d20. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d20Trace5, writeSuccess15d20Trace4,
        writeSuccess15d20Trace3, writeSuccess15d20Trace2,
        writeSuccess15d20Trace1, writeSuccess15d20NextPc,
        writeSuccessTraceTail, a15d20. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x15d20 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX11)
        (value := RVal_Bits (BV 64 8))
        (updated := RVal_Bits (BV 64 8)).
      - reflexivity.
      - unfold writeSuccess15d20Trace5, writeSuccess15d20Trace4,
          writeSuccess15d20Trace3, writeSuccess15d20Trace2,
          writeSuccess15d20Trace1, writeSuccessTraceTail, a15d20. cbn.
        constructor.
      - exact Hx12.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d20))
        (value := RVal_Bits writeSuccess15d20NextPc)
        (updated := RVal_Bits writeSuccess15d20NextPc).
      - reflexivity.
      - unfold writeSuccess15d20Trace6, writeSuccess15d20Trace5,
          writeSuccess15d20Trace4, writeSuccess15d20Trace3,
          writeSuccess15d20Trace2, writeSuccess15d20Trace1,
          writeSuccessTraceTail, a15d20. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15d24) (trace := a15d24).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x15d24).
      unfold writeSuccess15d20Regs. rewrite lookup_insert.
      rewrite writeSuccess15d20NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15d24), a15d24.
    cbn. unfold writeSuccess15d20Regs. rewrite lookup_insert.
    rewrite writeSuccess15d20NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_15d20 (regs : reg_map) (global : seq_global_state) oldX11 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d20)) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d20Before regs global)
    (writeSuccess15d20Observations regs global)
    (writeSuccess15d20After regs global) /\
  (writeSuccess15d20After regs global).1.(seq_regs) =
    writeSuccess15d20Regs regs /\
  (writeSuccess15d20After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15d20Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  eapply segment_15d20_mstatus; eauto.
Qed.

Print Assumptions segment_15d20_mstatus.
Print Assumptions segment_15d20.
Print Assumptions writeSuccess15d20RegsLookupOther.
Print Assumptions writeSuccess15d20RegsDom.

Lemma segment_15d20_mstatus_covered (regs : reg_map) (global : seq_global_state)
    oldX11 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d20)) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d20Before regs global)
    observations after ->
  after = writeSuccess15d20After regs global /\
  observations = writeSuccess15d20Observations regs global.
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus Hsegment.
  destruct Hsegment as
    [Hstart done prefix labels spawned Hprefix Hnil Hdone Hobservations Hend].
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(unfold writeSuccess15d20Before, writeSuccess15694Local, a15d20;
      discriminate) Hnil HdoneNb) as
    (labels0 & local1 & global1 & spawned0 & prefix1 &
     Hobs0 & Hstep0 & Hnb1 & Hprefix1).
  pose (before1 := (local1, global1)).
  inversion Hstep0 as [? ? ? ? ? ? ? Hnb0 Htrace0 Hsem0]; subst.
  unfold writeSuccess15d20Before, writeSuccess15694Local, a15d20 in Htrace0.
  cbn in Htrace0. inversion Htrace0; subst. cbn in Hsem0.
  destruct Hsem0 as (-> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix1
    ltac:(unfold before1; cbn; discriminate) Hnil HdoneNb) as
    (labels1 & local2 & global2 & spawned1 & prefix2 &
     Hobs1 & Hstep1 & Hnb2 & Hprefix2).
  pose (before2 := (local2, global2)).
  eapply writeSuccessAssumeCovered in Hstep1.
  2: reflexivity.
  2: exact Hmstatus.
  destruct Hstep1 as (-> & -> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix2
    ltac:(unfold before2; cbn; discriminate) Hnil HdoneNb) as
    (labels2 & local3 & global3 & spawned2 & prefix3 &
     Hobs2 & Hstep2 & Hnb3 & Hprefix3).
  pose (before3 := (local3, global3)).
  inversion Hstep2 as [? ? ? ? ? ? ? Hnb2' Htrace2 Hsem2]; subst.
  unfold before2, writeSuccess15d20Trace2, writeSuccess15d20Trace1,
    writeSuccessTraceTail, a15d20 in Htrace2. cbn in Htrace2.
  inversion Htrace2; subst. cbn in Hsem2.
  destruct Hsem2 as (-> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix3
    ltac:(unfold before3; cbn; discriminate) Hnil HdoneNb) as
    (labels3 & local4 & global4 & spawned3 & prefix4 &
     Hobs3 & Hstep3 & Hnb4 & Hprefix4).
  pose (before4 := (local4, global4)).
  eapply writeSuccessReadRegCovered in Hstep3.
  2: reflexivity.
  2: exact Hpc.
  2: reflexivity.
  2: exact Hnb4.
  destruct Hstep3 as (-> & -> & -> & -> & HsymbolicPc).
  cbn in HsymbolicPc. inversion HsymbolicPc as [HpcValue].
  assert (HpcBits : @BV 64 n0 Heq0 = Z_to_bv 64 0x15d20).
  { apply bv_eq. cbn. exact HpcValue. }
  repeat match goal with
  | H : context [@BV 64 n0 Heq0] |- _ => rewrite HpcBits in H
  end.

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix4
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels4 & local5 & global5 & spawned4 & prefix5 &
     Hobs4 & Hstep4 & Hnb5 & Hprefix5).
  pose (before5 := (local5, global5)).
  eapply writeSuccessDefineConstCovered in Hstep4.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep4 as (-> & -> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix5
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels5 & local6 & global6 & spawned5 & prefix6 &
     Hobs5 & Hstep5 & Hnb6 & Hprefix6).
  pose (before6 := (local6, global6)).
  eapply writeSuccessWriteRegCovered in Hstep5.
  2: reflexivity.
  2: exact Hx12.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep5 as (-> & -> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix6
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels6 & local7 & global7 & spawned6 & prefix7 &
     Hobs6 & Hstep6 & Hnb7 & Hprefix7).
  eapply writeSuccessWriteRegCovered in Hstep6.
  2: reflexivity.
  2: rewrite lookup_insert_ne; last done; exact Hpc.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep6 as (-> & -> & -> & ->).

  inversion Hprefix7; subst.
  2: contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity.
  2: { unfold writeSuccess15d20Regs. rewrite lookup_insert. reflexivity. }
  2: exact Hnext.
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned.
  destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal, Hend |- *.
  subst afterLocal afterGlobal.
  split.
  - reflexivity.
  - unfold writeSuccess15d20Observations,
      writeSuccess15d20PrefixObservations.
    cbn in *.
    fold writeSuccess15d20NextPc.
    rewrite HpcBits.
    reflexivity.
Qed.

Lemma segment_15d20_covered (regs : reg_map) (global : seq_global_state)
    oldX11 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d20)) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d20Before regs global)
    observations after ->
  after = writeSuccess15d20After regs global /\
  observations = writeSuccess15d20Observations regs global.
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus Hsegment.
  eapply segment_15d20_mstatus_covered; eauto.
Qed.

Print Assumptions segment_15d20_mstatus_covered.
Print Assumptions segment_15d20_covered.
