From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a1569c.
Require Import IslaTraces.write_success_90.a156a0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk00.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk01.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk02.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk03.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk04.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk05.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk06.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk07.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk08.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk09.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk10.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk11.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk12.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk13.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk14.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk15.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk16.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessTraceTail (trace : isla_trace) : isla_trace :=
  match trace with tcons _ rest => rest | _ => tnil end.

Definition writeSuccess1569cMstatus : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccess1569cTrace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a1569c).
Definition writeSuccess1569cTrace2 := writeSuccessTraceTail writeSuccess1569cTrace1.
Definition writeSuccess1569cTrace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x1569c)) 3
    (writeSuccessTraceTail writeSuccess1569cTrace2).
Definition writeSuccess1569cTrace4 := writeSuccessTraceTail writeSuccess1569cTrace3.
Definition writeSuccess1569cNextPc : bv 64 :=
  (Z_to_bv 64 0x1569c + BV 64 4)%bv.
Definition writeSuccess1569cTrace5 :=
  subst_trace (Val_Bits writeSuccess1569cNextPc) 4
    (writeSuccessTraceTail writeSuccess1569cTrace4).
Definition writeSuccess1569cTrace6 (sp : bv 64) :=
  subst_trace (Val_Bits sp) 5 (writeSuccessTraceTail writeSuccess1569cTrace5).
Definition writeSuccess1569cTrace7 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess1569cTrace6 sp).
Definition writeSuccess1569cTrace8 (sp : bv 64) :=
  subst_trace (Val_Bits (sp + BV 64 0)%bv) 6
    (writeSuccessTraceTail (writeSuccess1569cTrace7 sp)).
Definition writeSuccess1569cTrace9 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess1569cTrace8 sp).
Definition writeSuccess1569cTrace10 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess1569cTrace9 sp).

Definition writeSuccess1569cRegs (regs : reg_map) (sp : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess1569cNextPc]>
    (<["x11" := RVal_Bits (sp + BV 64 0)%bv]> regs).

Lemma writeSuccess1569cRegsLookupOther regs sp reg :
  reg <> "PC" ->
  reg <> "x11" ->
  writeSuccess1569cRegs regs sp !! reg = regs !! reg.
Proof.
  intros Hpc Hx10. unfold writeSuccess1569cRegs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Definition writeSuccess1569cLocal (trace : isla_trace) (regs : reg_map) :
    seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccess1569cBefore (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess1569cLocal a1569c regs, global).

Definition writeSuccess1569cAfter (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) : IslaState :=
  (writeSuccess1569cLocal a156a0 (writeSuccess1569cRegs regs sp), global).

Definition writeSuccess1569cObservation (local : seq_local_state)
    (global : seq_global_state) : IslaMicroObservation := {|
  microLabels := [];
  microAfter := (local, global)
|}.

Lemma writeSuccess1569cNextPcExact :
  writeSuccess1569cNextPc = Z_to_bv 64 0x156a0.
Proof. unfold writeSuccess1569cNextPc. bv_solve. Qed.

Definition writeSuccess1569cPrefixObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  [writeSuccess1569cObservation
     (writeSuccess1569cLocal writeSuccess1569cTrace1 regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal writeSuccess1569cTrace2 regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal writeSuccess1569cTrace3 regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal writeSuccess1569cTrace4 regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal writeSuccess1569cTrace5 regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal (writeSuccess1569cTrace6 sp) regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal (writeSuccess1569cTrace7 sp) regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal (writeSuccess1569cTrace8 sp) regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal (writeSuccess1569cTrace9 sp)
       (<["x11" := RVal_Bits (sp + BV 64 0)%bv]> regs)) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal (writeSuccess1569cTrace10 sp)
       (writeSuccess1569cRegs regs sp)) global].

Definition writeSuccess1569cObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  writeSuccess1569cPrefixObservations regs global sp ++
  [writeSuccess1569cObservation
     (writeSuccess1569cAfter regs global sp).1 global].

Lemma writeSuccess1569cMstatusFromTraceAssumptions regs global :
  writeSuccessTraceAssumptions (writeSuccess1569cBefore regs global) ->
  eval_a_exp regs writeSuccess1569cMstatus = Some (Val_Bool true).
Proof.
  intros Hassumptions.
  apply Forall_forall with
    (x := Assume writeSuccess1569cMstatus Mk_annot :t: tnil)
    in Hassumptions.
  - exact Hassumptions.
  - unfold writeSuccessTraceAssumptionEvents.
    rewrite elem_of_list_In.
    apply in_concat. exists writeSuccessTraceAssumptionsChunk11.
    split.
    + cbn. tauto.
    + unfold writeSuccessTraceAssumptionsChunk11,
        writeSuccess1569cMstatus. cbn. tauto.
Qed.

Lemma writeSuccess1569cTakeStep before observations done :
  IslaInstructionPrefixPath before observations done ->
  before.1.(seq_trace) <> tnil ->
  done.1.(seq_trace) = tnil ->
  done.1.(seq_nb_state) = false ->
  exists labels middleLocal middleGlobal spawned rest,
    observations =
      {| microLabels := labels;
         microAfter := (middleLocal, middleGlobal) |} :: rest /\
    seq_step before.1 before.2 labels middleLocal middleGlobal spawned /\
    middleLocal.(seq_nb_state) = false /\
    IslaInstructionPrefixPath (middleLocal, middleGlobal) rest done.
Proof.
  intros Hpath Hsource HdoneTrace HdoneNb.
  exact (writeSuccessInstructionPrefixTakeStep before observations done
    Hsource HdoneTrace HdoneNb Hpath).
Qed.

Lemma segment_1569c_mstatus (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX11 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1569c)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  eval_a_exp regs writeSuccess1569cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess1569cBefore regs global)
    (writeSuccess1569cObservations regs global sp)
    (writeSuccess1569cAfter regs global sp) /\
  (writeSuccess1569cAfter regs global sp).1.(seq_regs) =
    writeSuccess1569cRegs regs sp /\
  (writeSuccess1569cAfter regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess1569cObservations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess1569cObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess1569cLocal tnil (writeSuccess1569cRegs regs sp), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x1569c), a1569c.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess1569cPrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1569cBefore, writeSuccess1569cLocal,
        writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1569cTrace2, writeSuccess1569cTrace1,
        writeSuccessTraceTail, a1569c. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x1569c). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x1569c))
        (value := RVal_Bits (Z_to_bv 64 0x1569c)).
      - reflexivity.
      - unfold writeSuccess1569cTrace3, writeSuccess1569cTrace2,
          writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1569cTrace5, writeSuccess1569cTrace4, writeSuccess1569cTrace3,
        writeSuccess1569cTrace2, writeSuccess1569cTrace1,
        writeSuccess1569cNextPc, writeSuccessTraceTail, a1569c. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x1569c + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1569cTrace5, writeSuccess1569cTrace4,
        writeSuccess1569cTrace3, writeSuccess1569cTrace2,
        writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c. cbn.
      apply DeclareConstBitVecS' with (b := sp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits sp) (value := RVal_Bits sp).
      - reflexivity.
      - unfold writeSuccess1569cTrace6, writeSuccess1569cTrace5,
          writeSuccess1569cTrace4, writeSuccess1569cTrace3,
          writeSuccess1569cTrace2, writeSuccess1569cTrace1,
          writeSuccessTraceTail, a1569c. cbn. constructor.
      - exact Hsp.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1569cTrace7, writeSuccess1569cTrace6,
        writeSuccess1569cTrace5, writeSuccess1569cTrace4,
        writeSuccess1569cTrace3, writeSuccess1569cTrace2,
        writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c. cbn.
      eapply DefineConstS with (v := Val_Bits (sp + BV 64 0)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX11)
        (value := RVal_Bits (sp + BV 64 0)%bv)
        (updated := RVal_Bits (sp + BV 64 0)%bv).
      - reflexivity.
      - unfold writeSuccess1569cTrace8, writeSuccess1569cTrace7,
          writeSuccess1569cTrace6, writeSuccess1569cTrace5,
          writeSuccess1569cTrace4, writeSuccess1569cTrace3,
          writeSuccess1569cTrace2, writeSuccess1569cTrace1,
          writeSuccessTraceTail, a1569c. cbn. constructor.
      - exact Hx10.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x1569c))
        (value := RVal_Bits writeSuccess1569cNextPc)
        (updated := RVal_Bits writeSuccess1569cNextPc).
      - reflexivity.
      - unfold writeSuccess1569cTrace9, writeSuccess1569cTrace8,
          writeSuccess1569cTrace7, writeSuccess1569cTrace6,
          writeSuccess1569cTrace5, writeSuccess1569cTrace4,
          writeSuccess1569cTrace3, writeSuccess1569cTrace2,
          writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c. cbn.
        constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156a0) (trace := a156a0).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x156a0).
      unfold writeSuccess1569cRegs. rewrite lookup_insert.
      rewrite writeSuccess1569cNextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156a0), a156a0.
    cbn. unfold writeSuccess1569cRegs. rewrite lookup_insert.
    rewrite writeSuccess1569cNextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_1569c (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX11 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1569c)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  writeSuccessTraceAssumptions (writeSuccess1569cBefore regs global) ->
  IslaInstructionSegment (writeSuccess1569cBefore regs global)
    (writeSuccess1569cObservations regs global sp)
    (writeSuccess1569cAfter regs global sp) /\
  (writeSuccess1569cAfter regs global sp).1.(seq_regs) =
    writeSuccess1569cRegs regs sp /\
  (writeSuccess1569cAfter regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess1569cObservations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hassumptions.
  eapply segment_1569c_mstatus; eauto.
  exact (writeSuccess1569cMstatusFromTraceAssumptions
    regs global Hassumptions).
Qed.

Print Assumptions writeSuccess1569cMstatusFromTraceAssumptions.
Print Assumptions writeSuccess1569cNextPcExact.
Print Assumptions segment_1569c_mstatus.
Print Assumptions segment_1569c.
Print Assumptions writeSuccess1569cRegsLookupOther.

Lemma segment_1569c_mstatus_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX11 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1569c)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  eval_a_exp regs writeSuccess1569cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess1569cBefore regs global)
    observations after ->
  after = writeSuccess1569cAfter regs global sp /\
  observations = writeSuccess1569cObservations regs global sp.
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus Hsegment.
  destruct Hsegment as
    [Hstart done prefix labels spawned Hprefix Hnil Hdone Hobservations Hend].
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  assert (Hsource0 :
    (writeSuccess1569cBefore regs global).1.(seq_trace) <> tnil).
  { unfold writeSuccess1569cBefore, writeSuccess1569cLocal, a1569c.
    discriminate. }
  destruct (writeSuccess1569cTakeStep
    _ _ _ Hprefix Hsource0 Hnil HdoneNb) as
    (labels0 & local1 & global1 & spawned0 & prefix1 &
     Hobs0 & Hstep0 & Hnb1 & Hprefix1).
  pose (before1 := (local1, global1)).
  inversion Hstep0 as [? ? ? ? ? ? ? Hnb0 Htrace0 Hsem0]; subst.
  unfold writeSuccess1569cBefore, writeSuccess1569cLocal, a1569c in Htrace0.
  cbn in Htrace0. inversion Htrace0; subst. cbn in Hsem0.
  destruct Hsem0 as (-> & -> & ->).

  destruct (writeSuccess1569cTakeStep _ _ _ Hprefix1
    ltac:(unfold before1; cbn; discriminate) Hnil HdoneNb) as
    (labels1 & local2 & global2 & spawned1 & prefix2 &
     Hobs1 & Hstep1 & Hnb2 & Hprefix2).
  pose (before2 := (local2, global2)).
  eapply writeSuccessAssumeCovered in Hstep1.
  2: reflexivity.
  2: exact Hmstatus.
  destruct Hstep1 as (-> & -> & -> & ->).

  destruct (writeSuccess1569cTakeStep _ _ _ Hprefix2
    ltac:(unfold before2; cbn; discriminate) Hnil HdoneNb) as
    (labels2 & local3 & global3 & spawned2 & prefix3 &
     Hobs2 & Hstep2 & Hnb3 & Hprefix3).
  pose (before3 := (local3, global3)).
  inversion Hstep2 as [? ? ? ? ? ? ? Hnb2' Htrace2 Hsem2]; subst.
  unfold before2, writeSuccess1569cTrace2, writeSuccess1569cTrace1,
    writeSuccessTraceTail, a1569c in Htrace2. cbn in Htrace2.
  inversion Htrace2; subst. cbn in Hsem2.
  destruct Hsem2 as (-> & -> & ->).

  destruct (writeSuccess1569cTakeStep _ _ _ Hprefix3
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
  assert (HpcBits : @BV 64 n0 Heq0 = Z_to_bv 64 0x1569c).
  { apply bv_eq. cbn. exact HpcValue. }
  repeat match goal with
  | H : context [@BV 64 n0 Heq0] |- _ => rewrite HpcBits in H
  end.

  destruct (writeSuccess1569cTakeStep _ _ _ Hprefix4
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels4 & local5 & global5 & spawned4 & prefix5 &
     Hobs4 & Hstep4 & Hnb5 & Hprefix5).
  pose (before5 := (local5, global5)).
  eapply writeSuccessDefineConstCovered in Hstep4.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep4 as (-> & -> & -> & ->).

  destruct (writeSuccess1569cTakeStep _ _ _ Hprefix5
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels5 & local6 & global6 & spawned5 & prefix6 &
     Hobs5 & Hstep5 & Hnb6 & Hprefix6).
  pose (before6 := (local6, global6)).
  inversion Hstep5 as [? ? ? ? ? ? ? Hnb5' Htrace5 Hsem5]; subst.
  unfold before5, writeSuccess1569cTrace5, writeSuccess1569cTrace4,
    writeSuccess1569cTrace3, writeSuccess1569cTrace2,
    writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c in Htrace5.
  cbn in Htrace5. inversion Htrace5; subst. cbn in Hsem5.
  destruct Hsem5 as (-> & -> & ->).

  destruct (writeSuccess1569cTakeStep _ _ _ Hprefix6
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels6 & local7 & global7 & spawned6 & prefix7 &
     Hobs6 & Hstep6 & Hnb7 & Hprefix7).
  pose (before7 := (local7, global7)).
  eapply writeSuccessReadRegCovered in Hstep6.
  2: reflexivity.
  2: exact Hsp.
  2: reflexivity.
  2: exact Hnb7.
  destruct Hstep6 as (-> & -> & -> & -> & HsymbolicSp).
  cbn in HsymbolicSp. inversion HsymbolicSp as [HspValue].
  pose proof (inj_pair2_eq_dec N (Coq.NArith.BinNat.N.eq_dec)
    (fun width => bv width) 64%N (BV 64 n0) sp HspValue) as HspBits.
  repeat match goal with
  | H : context [BV 64 n0] |- _ => rewrite HspBits in H
  end.

  destruct (writeSuccess1569cTakeStep _ _ _ Hprefix7
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels7 & local8 & global8 & spawned7 & prefix8 &
     Hobs7 & Hstep7 & Hnb8 & Hprefix8).
  pose (before8 := (local8, global8)).
  eapply writeSuccessDefineConstCovered in Hstep7.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep7 as (-> & -> & -> & ->).

  destruct (writeSuccess1569cTakeStep _ _ _ Hprefix8
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels8 & local9 & global9 & spawned8 & prefix9 &
     Hobs8 & Hstep8 & Hnb9 & Hprefix9).
  pose (before9 := (local9, global9)).
  eapply writeSuccessWriteRegCovered in Hstep8.
  2: reflexivity.
  2: exact Hx10.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep8 as (-> & -> & -> & ->).

  destruct (writeSuccess1569cTakeStep _ _ _ Hprefix9
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels9 & local10 & global10 & spawned9 & prefix10 &
     Hobs9 & Hstep9 & Hnb10 & Hprefix10).
  eapply writeSuccessWriteRegCovered in Hstep9.
  2: reflexivity.
  2: rewrite lookup_insert_ne; last done; exact Hpc.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep9 as (-> & -> & -> & ->).

  inversion Hprefix10; subst.
  2: contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity.
  2: { unfold writeSuccess1569cRegs. rewrite lookup_insert. reflexivity. }
  2: exact Hnext.
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned.
  destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal, Hend |- *.
  subst afterLocal afterGlobal.
  split.
  - reflexivity.
  - unfold writeSuccess1569cObservations,
      writeSuccess1569cPrefixObservations.
    cbn in *.
    fold writeSuccess1569cNextPc.
    rewrite HpcBits.
    reflexivity.
Qed.

Lemma segment_1569c_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX11 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1569c)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  writeSuccessTraceAssumptions (writeSuccess1569cBefore regs global) ->
  IslaInstructionSegment (writeSuccess1569cBefore regs global)
    observations after ->
  after = writeSuccess1569cAfter regs global sp /\
  observations = writeSuccess1569cObservations regs global sp.
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hassumptions Hsegment.
  eapply segment_1569c_mstatus_covered; eauto.
  exact (writeSuccess1569cMstatusFromTraceAssumptions
    regs global Hassumptions).
Qed.

Print Assumptions segment_1569c_mstatus_covered.
Print Assumptions segment_1569c_covered.
