From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101ec.
Require Import IslaTraces.write_success_02.a101f0.
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

Definition writeSuccess101ecMstatus : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccess101ecTrace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a101ec).
Definition writeSuccess101ecTrace2 := writeSuccessTraceTail writeSuccess101ecTrace1.
Definition writeSuccess101ecTrace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x101ec)) 3
    (writeSuccessTraceTail writeSuccess101ecTrace2).
Definition writeSuccess101ecTrace4 := writeSuccessTraceTail writeSuccess101ecTrace3.
Definition writeSuccess101ecNextPc : bv 64 :=
  (Z_to_bv 64 0x101ec + BV 64 4)%bv.
Definition writeSuccess101ecTrace5 :=
  subst_trace (Val_Bits writeSuccess101ecNextPc) 4
    (writeSuccessTraceTail writeSuccess101ecTrace4).
Definition writeSuccess101ecTrace6 (sp : bv 64) :=
  subst_trace (Val_Bits sp) 5 (writeSuccessTraceTail writeSuccess101ecTrace5).
Definition writeSuccess101ecTrace7 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess101ecTrace6 sp).
Definition writeSuccess101ecTrace8 (sp : bv 64) :=
  subst_trace (Val_Bits (sp + BV 64 1)%bv) 6
    (writeSuccessTraceTail (writeSuccess101ecTrace7 sp)).
Definition writeSuccess101ecTrace9 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess101ecTrace8 sp).
Definition writeSuccess101ecTrace10 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess101ecTrace9 sp).

Definition writeSuccess101ecRegs (regs : reg_map) (sp : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess101ecNextPc]>
    (<["x15" := RVal_Bits (sp + BV 64 1)%bv]> regs).

Lemma writeSuccess101ecRegsLookupOther regs sp reg :
  reg <> "PC" ->
  reg <> "x15" ->
  writeSuccess101ecRegs regs sp !! reg = regs !! reg.
Proof.
  intros Hpc Hx10. unfold writeSuccess101ecRegs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Definition writeSuccess101ecLocal (trace : isla_trace) (regs : reg_map) :
    seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccess101ecBefore (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess101ecLocal a101ec regs, global).

Definition writeSuccess101ecAfter (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) : IslaState :=
  (writeSuccess101ecLocal a101f0 (writeSuccess101ecRegs regs sp), global).

Definition writeSuccess101ecObservation (local : seq_local_state)
    (global : seq_global_state) : IslaMicroObservation := {|
  microLabels := [];
  microAfter := (local, global)
|}.

Lemma writeSuccess101ecNextPcExact :
  writeSuccess101ecNextPc = Z_to_bv 64 0x101f0.
Proof. unfold writeSuccess101ecNextPc. bv_solve. Qed.

Definition writeSuccess101ecPrefixObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  [writeSuccess101ecObservation
     (writeSuccess101ecLocal writeSuccess101ecTrace1 regs) global;
   writeSuccess101ecObservation
     (writeSuccess101ecLocal writeSuccess101ecTrace2 regs) global;
   writeSuccess101ecObservation
     (writeSuccess101ecLocal writeSuccess101ecTrace3 regs) global;
   writeSuccess101ecObservation
     (writeSuccess101ecLocal writeSuccess101ecTrace4 regs) global;
   writeSuccess101ecObservation
     (writeSuccess101ecLocal writeSuccess101ecTrace5 regs) global;
   writeSuccess101ecObservation
     (writeSuccess101ecLocal (writeSuccess101ecTrace6 sp) regs) global;
   writeSuccess101ecObservation
     (writeSuccess101ecLocal (writeSuccess101ecTrace7 sp) regs) global;
   writeSuccess101ecObservation
     (writeSuccess101ecLocal (writeSuccess101ecTrace8 sp) regs) global;
   writeSuccess101ecObservation
     (writeSuccess101ecLocal (writeSuccess101ecTrace9 sp)
       (<["x15" := RVal_Bits (sp + BV 64 1)%bv]> regs)) global;
   writeSuccess101ecObservation
     (writeSuccess101ecLocal (writeSuccess101ecTrace10 sp)
       (writeSuccess101ecRegs regs sp)) global].

Definition writeSuccess101ecObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  writeSuccess101ecPrefixObservations regs global sp ++
  [writeSuccess101ecObservation
     (writeSuccess101ecAfter regs global sp).1 global].

Lemma writeSuccess101ecMstatusFromTraceAssumptions regs global :
  writeSuccessTraceAssumptions (writeSuccess101ecBefore regs global) ->
  eval_a_exp regs writeSuccess101ecMstatus = Some (Val_Bool true).
Proof.
  intros Hassumptions.
  apply Forall_forall with
    (x := Assume writeSuccess101ecMstatus Mk_annot :t: tnil)
    in Hassumptions.
  - exact Hassumptions.
  - unfold writeSuccessTraceAssumptionEvents.
    rewrite elem_of_list_In.
    apply in_concat. exists writeSuccessTraceAssumptionsChunk11.
    split.
    + cbn. tauto.
    + unfold writeSuccessTraceAssumptionsChunk11,
        writeSuccess101ecMstatus. cbn. tauto.
Qed.

Lemma writeSuccess101ecTakeStep before observations done :
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

Lemma segment_101ec_mstatus (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX15 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101ec)) ->
  regs !! "x15" = Some (RVal_Bits sp) ->
  regs !! "x15" = Some oldX15 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f0 = Some a101f0 ->
  eval_a_exp regs writeSuccess101ecMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101ecBefore regs global)
    (writeSuccess101ecObservations regs global sp)
    (writeSuccess101ecAfter regs global sp) /\
  (writeSuccess101ecAfter regs global sp).1.(seq_regs) =
    writeSuccess101ecRegs regs sp /\
  (writeSuccess101ecAfter regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess101ecObservations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess101ecObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess101ecLocal tnil (writeSuccess101ecRegs regs sp), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x101ec), a101ec.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess101ecPrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess101ecBefore, writeSuccess101ecLocal,
        writeSuccess101ecTrace1, writeSuccessTraceTail, a101ec. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess101ecTrace1, writeSuccessTraceTail, a101ec. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess101ecTrace2, writeSuccess101ecTrace1,
        writeSuccessTraceTail, a101ec. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x101ec). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x101ec))
        (value := RVal_Bits (Z_to_bv 64 0x101ec)).
      - reflexivity.
      - unfold writeSuccess101ecTrace3, writeSuccess101ecTrace2,
          writeSuccess101ecTrace1, writeSuccessTraceTail, a101ec. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess101ecTrace5, writeSuccess101ecTrace4, writeSuccess101ecTrace3,
        writeSuccess101ecTrace2, writeSuccess101ecTrace1,
        writeSuccess101ecNextPc, writeSuccessTraceTail, a101ec. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x101ec + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess101ecTrace5, writeSuccess101ecTrace4,
        writeSuccess101ecTrace3, writeSuccess101ecTrace2,
        writeSuccess101ecTrace1, writeSuccessTraceTail, a101ec. cbn.
      apply DeclareConstBitVecS' with (b := sp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits sp) (value := RVal_Bits sp).
      - reflexivity.
      - unfold writeSuccess101ecTrace6, writeSuccess101ecTrace5,
          writeSuccess101ecTrace4, writeSuccess101ecTrace3,
          writeSuccess101ecTrace2, writeSuccess101ecTrace1,
          writeSuccessTraceTail, a101ec. cbn. constructor.
      - exact Hsp.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess101ecTrace7, writeSuccess101ecTrace6,
        writeSuccess101ecTrace5, writeSuccess101ecTrace4,
        writeSuccess101ecTrace3, writeSuccess101ecTrace2,
        writeSuccess101ecTrace1, writeSuccessTraceTail, a101ec. cbn.
      eapply DefineConstS with (v := Val_Bits (sp + BV 64 1)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX15)
        (value := RVal_Bits (sp + BV 64 1)%bv)
        (updated := RVal_Bits (sp + BV 64 1)%bv).
      - reflexivity.
      - unfold writeSuccess101ecTrace8, writeSuccess101ecTrace7,
          writeSuccess101ecTrace6, writeSuccess101ecTrace5,
          writeSuccess101ecTrace4, writeSuccess101ecTrace3,
          writeSuccess101ecTrace2, writeSuccess101ecTrace1,
          writeSuccessTraceTail, a101ec. cbn. constructor.
      - exact Hx10.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x101ec))
        (value := RVal_Bits writeSuccess101ecNextPc)
        (updated := RVal_Bits writeSuccess101ecNextPc).
      - reflexivity.
      - unfold writeSuccess101ecTrace9, writeSuccess101ecTrace8,
          writeSuccess101ecTrace7, writeSuccess101ecTrace6,
          writeSuccess101ecTrace5, writeSuccess101ecTrace4,
          writeSuccess101ecTrace3, writeSuccess101ecTrace2,
          writeSuccess101ecTrace1, writeSuccessTraceTail, a101ec. cbn.
        constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a101f0) (trace := a101f0).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x101f0).
      unfold writeSuccess101ecRegs. rewrite lookup_insert.
      rewrite writeSuccess101ecNextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x101f0), a101f0.
    cbn. unfold writeSuccess101ecRegs. rewrite lookup_insert.
    rewrite writeSuccess101ecNextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_101ec (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX15 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101ec)) ->
  regs !! "x15" = Some (RVal_Bits sp) ->
  regs !! "x15" = Some oldX15 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f0 = Some a101f0 ->
  writeSuccessTraceAssumptions (writeSuccess101ecBefore regs global) ->
  IslaInstructionSegment (writeSuccess101ecBefore regs global)
    (writeSuccess101ecObservations regs global sp)
    (writeSuccess101ecAfter regs global sp) /\
  (writeSuccess101ecAfter regs global sp).1.(seq_regs) =
    writeSuccess101ecRegs regs sp /\
  (writeSuccess101ecAfter regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess101ecObservations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hassumptions.
  eapply segment_101ec_mstatus; eauto.
  exact (writeSuccess101ecMstatusFromTraceAssumptions
    regs global Hassumptions).
Qed.

Print Assumptions writeSuccess101ecMstatusFromTraceAssumptions.
Print Assumptions writeSuccess101ecNextPcExact.
Print Assumptions segment_101ec_mstatus.
Print Assumptions segment_101ec.
Print Assumptions writeSuccess101ecRegsLookupOther.
