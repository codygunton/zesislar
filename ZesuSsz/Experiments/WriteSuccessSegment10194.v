From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a10194.
Require Import IslaTraces.write_success_01.a10198.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessTraceTail (trace : isla_trace) : isla_trace :=
  match trace with tcons _ rest => rest | _ => tnil end.

Definition writeSuccess10194Mstatus : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccess10194Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a10194).
Definition writeSuccess10194Trace2 := writeSuccessTraceTail writeSuccess10194Trace1.
Definition writeSuccess10194Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x10194)) 3
    (writeSuccessTraceTail writeSuccess10194Trace2).
Definition writeSuccess10194Trace4 := writeSuccessTraceTail writeSuccess10194Trace3.
Definition writeSuccess10194NextPc : bv 64 :=
  (Z_to_bv 64 0x10194 + BV 64 4)%bv.
Definition writeSuccess10194Trace5 :=
  subst_trace (Val_Bits writeSuccess10194NextPc) 4
    (writeSuccessTraceTail writeSuccess10194Trace4).
Definition writeSuccess10194Trace6 (sp : bv 64) :=
  subst_trace (Val_Bits sp) 5 (writeSuccessTraceTail writeSuccess10194Trace5).
Definition writeSuccess10194Trace7 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess10194Trace6 sp).
Definition writeSuccess10194Trace8 (sp : bv 64) :=
  subst_trace (Val_Bits (sp + BV 64 18446744073709551400)%bv) 6
    (writeSuccessTraceTail (writeSuccess10194Trace7 sp)).
Definition writeSuccess10194Trace9 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess10194Trace8 sp).
Definition writeSuccess10194Trace10 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess10194Trace9 sp).

Definition writeSuccess10194Regs (regs : reg_map) (sp : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess10194NextPc]>
    (<["x5" := RVal_Bits (sp + BV 64 18446744073709551400)%bv]> regs).

Lemma writeSuccess10194RegsLookupOther regs sp reg :
  reg <> "PC" ->
  reg <> "x5" ->
  writeSuccess10194Regs regs sp !! reg = regs !! reg.
Proof.
  intros Hpc Hx10. unfold writeSuccess10194Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Definition writeSuccess10194Local (trace : isla_trace) (regs : reg_map) :
    seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccess10194Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess10194Local a10194 regs, global).

Definition writeSuccess10194After (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) : IslaState :=
  (writeSuccess10194Local a10198 (writeSuccess10194Regs regs sp), global).

Definition writeSuccess10194Observation (local : seq_local_state)
    (global : seq_global_state) : IslaMicroObservation := {|
  microLabels := [];
  microAfter := (local, global)
|}.

Lemma writeSuccess10194NextPcExact :
  writeSuccess10194NextPc = Z_to_bv 64 0x10198.
Proof. unfold writeSuccess10194NextPc. bv_solve. Qed.

Definition writeSuccess10194PrefixObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  [writeSuccess10194Observation
     (writeSuccess10194Local writeSuccess10194Trace1 regs) global;
   writeSuccess10194Observation
     (writeSuccess10194Local writeSuccess10194Trace2 regs) global;
   writeSuccess10194Observation
     (writeSuccess10194Local writeSuccess10194Trace3 regs) global;
   writeSuccess10194Observation
     (writeSuccess10194Local writeSuccess10194Trace4 regs) global;
   writeSuccess10194Observation
     (writeSuccess10194Local writeSuccess10194Trace5 regs) global;
   writeSuccess10194Observation
     (writeSuccess10194Local (writeSuccess10194Trace6 sp) regs) global;
   writeSuccess10194Observation
     (writeSuccess10194Local (writeSuccess10194Trace7 sp) regs) global;
   writeSuccess10194Observation
     (writeSuccess10194Local (writeSuccess10194Trace8 sp) regs) global;
   writeSuccess10194Observation
     (writeSuccess10194Local (writeSuccess10194Trace9 sp)
       (<["x5" := RVal_Bits (sp + BV 64 18446744073709551400)%bv]> regs)) global;
   writeSuccess10194Observation
     (writeSuccess10194Local (writeSuccess10194Trace10 sp)
       (writeSuccess10194Regs regs sp)) global].

Definition writeSuccess10194Observations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  writeSuccess10194PrefixObservations regs global sp ++
  [writeSuccess10194Observation
     (writeSuccess10194After regs global sp).1 global].

Lemma writeSuccess10194TakeStep before observations done :
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

Lemma segment_10194_mstatus (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX5 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10194)) ->
  regs !! "x5" = Some (RVal_Bits sp) ->
  regs !! "x5" = Some oldX5 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10194 = Some a10194 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10198 = Some a10198 ->
  eval_a_exp regs writeSuccess10194Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess10194Before regs global)
    (writeSuccess10194Observations regs global sp)
    (writeSuccess10194After regs global sp) /\
  (writeSuccess10194After regs global sp).1.(seq_regs) =
    writeSuccess10194Regs regs sp /\
  (writeSuccess10194After regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess10194Observations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess10194Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess10194Local tnil (writeSuccess10194Regs regs sp), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x10194), a10194.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess10194PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess10194Before, writeSuccess10194Local,
        writeSuccess10194Trace1, writeSuccessTraceTail, a10194. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess10194Trace1, writeSuccessTraceTail, a10194. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess10194Trace2, writeSuccess10194Trace1,
        writeSuccessTraceTail, a10194. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x10194). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x10194))
        (value := RVal_Bits (Z_to_bv 64 0x10194)).
      - reflexivity.
      - unfold writeSuccess10194Trace3, writeSuccess10194Trace2,
          writeSuccess10194Trace1, writeSuccessTraceTail, a10194. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess10194Trace5, writeSuccess10194Trace4, writeSuccess10194Trace3,
        writeSuccess10194Trace2, writeSuccess10194Trace1,
        writeSuccess10194NextPc, writeSuccessTraceTail, a10194. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x10194 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess10194Trace5, writeSuccess10194Trace4,
        writeSuccess10194Trace3, writeSuccess10194Trace2,
        writeSuccess10194Trace1, writeSuccessTraceTail, a10194. cbn.
      apply DeclareConstBitVecS' with (b := sp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits sp) (value := RVal_Bits sp).
      - reflexivity.
      - unfold writeSuccess10194Trace6, writeSuccess10194Trace5,
          writeSuccess10194Trace4, writeSuccess10194Trace3,
          writeSuccess10194Trace2, writeSuccess10194Trace1,
          writeSuccessTraceTail, a10194. cbn. constructor.
      - exact Hsp.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess10194Trace7, writeSuccess10194Trace6,
        writeSuccess10194Trace5, writeSuccess10194Trace4,
        writeSuccess10194Trace3, writeSuccess10194Trace2,
        writeSuccess10194Trace1, writeSuccessTraceTail, a10194. cbn.
      eapply DefineConstS with (v := Val_Bits (sp + BV 64 18446744073709551400)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX5)
        (value := RVal_Bits (sp + BV 64 18446744073709551400)%bv)
        (updated := RVal_Bits (sp + BV 64 18446744073709551400)%bv).
      - reflexivity.
      - unfold writeSuccess10194Trace8, writeSuccess10194Trace7,
          writeSuccess10194Trace6, writeSuccess10194Trace5,
          writeSuccess10194Trace4, writeSuccess10194Trace3,
          writeSuccess10194Trace2, writeSuccess10194Trace1,
          writeSuccessTraceTail, a10194. cbn. constructor.
      - exact Hx10.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x10194))
        (value := RVal_Bits writeSuccess10194NextPc)
        (updated := RVal_Bits writeSuccess10194NextPc).
      - reflexivity.
      - unfold writeSuccess10194Trace9, writeSuccess10194Trace8,
          writeSuccess10194Trace7, writeSuccess10194Trace6,
          writeSuccess10194Trace5, writeSuccess10194Trace4,
          writeSuccess10194Trace3, writeSuccess10194Trace2,
          writeSuccess10194Trace1, writeSuccessTraceTail, a10194. cbn.
        constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a10198) (trace := a10198).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x10198).
      unfold writeSuccess10194Regs. rewrite lookup_insert.
      rewrite writeSuccess10194NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x10198), a10198.
    cbn. unfold writeSuccess10194Regs. rewrite lookup_insert.
    rewrite writeSuccess10194NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_10194 (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX5 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10194)) ->
  regs !! "x5" = Some (RVal_Bits sp) ->
  regs !! "x5" = Some oldX5 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10194 = Some a10194 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10198 = Some a10198 ->
  eval_a_exp regs writeSuccess10194Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess10194Before regs global)
    (writeSuccess10194Observations regs global sp)
    (writeSuccess10194After regs global sp) /\
  (writeSuccess10194After regs global sp).1.(seq_regs) =
    writeSuccess10194Regs regs sp /\
  (writeSuccess10194After regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess10194Observations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  eapply segment_10194_mstatus; eauto.
Qed.

Print Assumptions writeSuccess10194NextPcExact.
Print Assumptions segment_10194_mstatus.
Print Assumptions segment_10194.
Print Assumptions writeSuccess10194RegsLookupOther.
