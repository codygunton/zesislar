From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156dc.
Require Import IslaTraces.write_success_95.a156e0.
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

Definition writeSuccess156dcMstatus : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccess156dcTrace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156dc).
Definition writeSuccess156dcTrace2 := writeSuccessTraceTail writeSuccess156dcTrace1.
Definition writeSuccess156dcTrace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156dc)) 3
    (writeSuccessTraceTail writeSuccess156dcTrace2).
Definition writeSuccess156dcTrace4 := writeSuccessTraceTail writeSuccess156dcTrace3.
Definition writeSuccess156dcNextPc : bv 64 :=
  (Z_to_bv 64 0x156dc + BV 64 4)%bv.
Definition writeSuccess156dcTrace5 :=
  subst_trace (Val_Bits writeSuccess156dcNextPc) 4
    (writeSuccessTraceTail writeSuccess156dcTrace4).
Definition writeSuccess156dcTrace6 (sp : bv 64) :=
  subst_trace (Val_Bits sp) 5 (writeSuccessTraceTail writeSuccess156dcTrace5).
Definition writeSuccess156dcTrace7 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess156dcTrace6 sp).
Definition writeSuccess156dcTrace8 (sp : bv 64) :=
  subst_trace (Val_Bits (sp + BV 64 48)%bv) 6
    (writeSuccessTraceTail (writeSuccess156dcTrace7 sp)).
Definition writeSuccess156dcTrace9 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess156dcTrace8 sp).
Definition writeSuccess156dcTrace10 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess156dcTrace9 sp).

Definition writeSuccess156dcRegs (regs : reg_map) (sp : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156dcNextPc]>
    (<["x8" := RVal_Bits (sp + BV 64 48)%bv]> regs).

Lemma writeSuccess156dcRegsLookupOther regs sp reg :
  reg <> "PC" ->
  reg <> "x8" ->
  writeSuccess156dcRegs regs sp !! reg = regs !! reg.
Proof.
  intros Hpc Hx10. unfold writeSuccess156dcRegs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Definition writeSuccess156dcLocal (trace : isla_trace) (regs : reg_map) :
    seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccess156dcBefore (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess156dcLocal a156dc regs, global).

Definition writeSuccess156dcAfter (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) : IslaState :=
  (writeSuccess156dcLocal a156e0 (writeSuccess156dcRegs regs sp), global).

Definition writeSuccess156dcObservation (local : seq_local_state)
    (global : seq_global_state) : IslaMicroObservation := {|
  microLabels := [];
  microAfter := (local, global)
|}.

Lemma writeSuccess156dcNextPcExact :
  writeSuccess156dcNextPc = Z_to_bv 64 0x156e0.
Proof. unfold writeSuccess156dcNextPc. bv_solve. Qed.

Definition writeSuccess156dcPrefixObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  [writeSuccess156dcObservation
     (writeSuccess156dcLocal writeSuccess156dcTrace1 regs) global;
   writeSuccess156dcObservation
     (writeSuccess156dcLocal writeSuccess156dcTrace2 regs) global;
   writeSuccess156dcObservation
     (writeSuccess156dcLocal writeSuccess156dcTrace3 regs) global;
   writeSuccess156dcObservation
     (writeSuccess156dcLocal writeSuccess156dcTrace4 regs) global;
   writeSuccess156dcObservation
     (writeSuccess156dcLocal writeSuccess156dcTrace5 regs) global;
   writeSuccess156dcObservation
     (writeSuccess156dcLocal (writeSuccess156dcTrace6 sp) regs) global;
   writeSuccess156dcObservation
     (writeSuccess156dcLocal (writeSuccess156dcTrace7 sp) regs) global;
   writeSuccess156dcObservation
     (writeSuccess156dcLocal (writeSuccess156dcTrace8 sp) regs) global;
   writeSuccess156dcObservation
     (writeSuccess156dcLocal (writeSuccess156dcTrace9 sp)
       (<["x8" := RVal_Bits (sp + BV 64 48)%bv]> regs)) global;
   writeSuccess156dcObservation
     (writeSuccess156dcLocal (writeSuccess156dcTrace10 sp)
       (writeSuccess156dcRegs regs sp)) global].

Definition writeSuccess156dcObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  writeSuccess156dcPrefixObservations regs global sp ++
  [writeSuccess156dcObservation
     (writeSuccess156dcAfter regs global sp).1 global].

Lemma writeSuccess156dcMstatusFromTraceAssumptions regs global :
  writeSuccessTraceAssumptions (writeSuccess156dcBefore regs global) ->
  eval_a_exp regs writeSuccess156dcMstatus = Some (Val_Bool true).
Proof.
  intros Hassumptions.
  apply Forall_forall with
    (x := Assume writeSuccess156dcMstatus Mk_annot :t: tnil)
    in Hassumptions.
  - exact Hassumptions.
  - unfold writeSuccessTraceAssumptionEvents.
    rewrite elem_of_list_In.
    apply in_concat. exists writeSuccessTraceAssumptionsChunk11.
    split.
    + cbn. tauto.
    + unfold writeSuccessTraceAssumptionsChunk11,
        writeSuccess156dcMstatus. cbn. tauto.
Qed.

Lemma writeSuccess156dcTakeStep before observations done :
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

Lemma segment_156dc_mstatus (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX8 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156dc)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x8" = Some oldX8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156dc = Some a156dc ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e0 = Some a156e0 ->
  eval_a_exp regs writeSuccess156dcMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156dcBefore regs global)
    (writeSuccess156dcObservations regs global sp)
    (writeSuccess156dcAfter regs global sp) /\
  (writeSuccess156dcAfter regs global sp).1.(seq_regs) =
    writeSuccess156dcRegs regs sp /\
  (writeSuccess156dcAfter regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156dcObservations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156dcObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess156dcLocal tnil (writeSuccess156dcRegs regs sp), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156dc), a156dc.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156dcPrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156dcBefore, writeSuccess156dcLocal,
        writeSuccess156dcTrace1, writeSuccessTraceTail, a156dc. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess156dcTrace1, writeSuccessTraceTail, a156dc. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156dcTrace2, writeSuccess156dcTrace1,
        writeSuccessTraceTail, a156dc. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156dc). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x156dc))
        (value := RVal_Bits (Z_to_bv 64 0x156dc)).
      - reflexivity.
      - unfold writeSuccess156dcTrace3, writeSuccess156dcTrace2,
          writeSuccess156dcTrace1, writeSuccessTraceTail, a156dc. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156dcTrace5, writeSuccess156dcTrace4, writeSuccess156dcTrace3,
        writeSuccess156dcTrace2, writeSuccess156dcTrace1,
        writeSuccess156dcNextPc, writeSuccessTraceTail, a156dc. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x156dc + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156dcTrace5, writeSuccess156dcTrace4,
        writeSuccess156dcTrace3, writeSuccess156dcTrace2,
        writeSuccess156dcTrace1, writeSuccessTraceTail, a156dc. cbn.
      apply DeclareConstBitVecS' with (b := sp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits sp) (value := RVal_Bits sp).
      - reflexivity.
      - unfold writeSuccess156dcTrace6, writeSuccess156dcTrace5,
          writeSuccess156dcTrace4, writeSuccess156dcTrace3,
          writeSuccess156dcTrace2, writeSuccess156dcTrace1,
          writeSuccessTraceTail, a156dc. cbn. constructor.
      - exact Hsp.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156dcTrace7, writeSuccess156dcTrace6,
        writeSuccess156dcTrace5, writeSuccess156dcTrace4,
        writeSuccess156dcTrace3, writeSuccess156dcTrace2,
        writeSuccess156dcTrace1, writeSuccessTraceTail, a156dc. cbn.
      eapply DefineConstS with (v := Val_Bits (sp + BV 64 48)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX8)
        (value := RVal_Bits (sp + BV 64 48)%bv)
        (updated := RVal_Bits (sp + BV 64 48)%bv).
      - reflexivity.
      - unfold writeSuccess156dcTrace8, writeSuccess156dcTrace7,
          writeSuccess156dcTrace6, writeSuccess156dcTrace5,
          writeSuccess156dcTrace4, writeSuccess156dcTrace3,
          writeSuccess156dcTrace2, writeSuccess156dcTrace1,
          writeSuccessTraceTail, a156dc. cbn. constructor.
      - exact Hx10.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x156dc))
        (value := RVal_Bits writeSuccess156dcNextPc)
        (updated := RVal_Bits writeSuccess156dcNextPc).
      - reflexivity.
      - unfold writeSuccess156dcTrace9, writeSuccess156dcTrace8,
          writeSuccess156dcTrace7, writeSuccess156dcTrace6,
          writeSuccess156dcTrace5, writeSuccess156dcTrace4,
          writeSuccess156dcTrace3, writeSuccess156dcTrace2,
          writeSuccess156dcTrace1, writeSuccessTraceTail, a156dc. cbn.
        constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156e0) (trace := a156e0).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x156e0).
      unfold writeSuccess156dcRegs. rewrite lookup_insert.
      rewrite writeSuccess156dcNextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156e0), a156e0.
    cbn. unfold writeSuccess156dcRegs. rewrite lookup_insert.
    rewrite writeSuccess156dcNextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_156dc (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX8 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156dc)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x8" = Some oldX8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156dc = Some a156dc ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e0 = Some a156e0 ->
  writeSuccessTraceAssumptions (writeSuccess156dcBefore regs global) ->
  IslaInstructionSegment (writeSuccess156dcBefore regs global)
    (writeSuccess156dcObservations regs global sp)
    (writeSuccess156dcAfter regs global sp) /\
  (writeSuccess156dcAfter regs global sp).1.(seq_regs) =
    writeSuccess156dcRegs regs sp /\
  (writeSuccess156dcAfter regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156dcObservations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hassumptions.
  eapply segment_156dc_mstatus; eauto.
  exact (writeSuccess156dcMstatusFromTraceAssumptions
    regs global Hassumptions).
Qed.

Print Assumptions writeSuccess156dcMstatusFromTraceAssumptions.
Print Assumptions writeSuccess156dcNextPcExact.
Print Assumptions segment_156dc_mstatus.
Print Assumptions segment_156dc.
Print Assumptions writeSuccess156dcRegsLookupOther.
