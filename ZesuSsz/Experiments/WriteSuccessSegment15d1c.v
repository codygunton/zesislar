From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d1c.
Require Import IslaTraces.write_success_07.a15d20.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessTraceTail (trace : isla_trace) : isla_trace :=
  match trace with tcons _ rest => rest | _ => tnil end.

Definition writeSuccess15d1cMstatus : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccess15d1cTrace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a15d1c).
Definition writeSuccess15d1cTrace2 := writeSuccessTraceTail writeSuccess15d1cTrace1.
Definition writeSuccess15d1cTrace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15d1c)) 3
    (writeSuccessTraceTail writeSuccess15d1cTrace2).
Definition writeSuccess15d1cTrace4 := writeSuccessTraceTail writeSuccess15d1cTrace3.
Definition writeSuccess15d1cNextPc : bv 64 :=
  (Z_to_bv 64 0x15d1c + BV 64 4)%bv.
Definition writeSuccess15d1cTrace5 :=
  subst_trace (Val_Bits writeSuccess15d1cNextPc) 4
    (writeSuccessTraceTail writeSuccess15d1cTrace4).
Definition writeSuccess15d1cTrace6 (sp : bv 64) :=
  subst_trace (Val_Bits sp) 5 (writeSuccessTraceTail writeSuccess15d1cTrace5).
Definition writeSuccess15d1cTrace7 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d1cTrace6 sp).
Definition writeSuccess15d1cTrace8 (sp : bv 64) :=
  subst_trace (Val_Bits (sp + BV 64 0)%bv) 6
    (writeSuccessTraceTail (writeSuccess15d1cTrace7 sp)).
Definition writeSuccess15d1cTrace9 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d1cTrace8 sp).
Definition writeSuccess15d1cTrace10 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d1cTrace9 sp).

Definition writeSuccess15d1cRegs (regs : reg_map) (sp : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess15d1cNextPc]>
    (<["x10" := RVal_Bits (sp + BV 64 0)%bv]> regs).

Lemma writeSuccess15d1cRegsLookupOther regs sp reg :
  reg <> "PC" ->
  reg <> "x10" ->
  writeSuccess15d1cRegs regs sp !! reg = regs !! reg.
Proof.
  intros Hpc Hx10. unfold writeSuccess15d1cRegs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Definition writeSuccess15d1cLocal (trace : isla_trace) (regs : reg_map) :
    seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccess15d1cBefore (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15d1cLocal a15d1c regs, global).

Definition writeSuccess15d1cAfter (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) : IslaState :=
  (writeSuccess15d1cLocal a15d20 (writeSuccess15d1cRegs regs sp), global).

Definition writeSuccess15d1cObservation (local : seq_local_state)
    (global : seq_global_state) : IslaMicroObservation := {|
  microLabels := [];
  microAfter := (local, global)
|}.

Lemma writeSuccess15d1cNextPcExact :
  writeSuccess15d1cNextPc = Z_to_bv 64 0x15d20.
Proof. unfold writeSuccess15d1cNextPc. bv_solve. Qed.

Definition writeSuccess15d1cPrefixObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  [writeSuccess15d1cObservation
     (writeSuccess15d1cLocal writeSuccess15d1cTrace1 regs) global;
   writeSuccess15d1cObservation
     (writeSuccess15d1cLocal writeSuccess15d1cTrace2 regs) global;
   writeSuccess15d1cObservation
     (writeSuccess15d1cLocal writeSuccess15d1cTrace3 regs) global;
   writeSuccess15d1cObservation
     (writeSuccess15d1cLocal writeSuccess15d1cTrace4 regs) global;
   writeSuccess15d1cObservation
     (writeSuccess15d1cLocal writeSuccess15d1cTrace5 regs) global;
   writeSuccess15d1cObservation
     (writeSuccess15d1cLocal (writeSuccess15d1cTrace6 sp) regs) global;
   writeSuccess15d1cObservation
     (writeSuccess15d1cLocal (writeSuccess15d1cTrace7 sp) regs) global;
   writeSuccess15d1cObservation
     (writeSuccess15d1cLocal (writeSuccess15d1cTrace8 sp) regs) global;
   writeSuccess15d1cObservation
     (writeSuccess15d1cLocal (writeSuccess15d1cTrace9 sp)
       (<["x10" := RVal_Bits (sp + BV 64 0)%bv]> regs)) global;
   writeSuccess15d1cObservation
     (writeSuccess15d1cLocal (writeSuccess15d1cTrace10 sp)
       (writeSuccess15d1cRegs regs sp)) global].

Definition writeSuccess15d1cObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  writeSuccess15d1cPrefixObservations regs global sp ++
  [writeSuccess15d1cObservation
     (writeSuccess15d1cAfter regs global sp).1 global].

Lemma writeSuccess15d1cTakeStep before observations done :
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

Lemma segment_15d1c_mstatus (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d1c)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d1c = Some a15d1c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 ->
  eval_a_exp regs writeSuccess15d1cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d1cBefore regs global)
    (writeSuccess15d1cObservations regs global sp)
    (writeSuccess15d1cAfter regs global sp) /\
  (writeSuccess15d1cAfter regs global sp).1.(seq_regs) =
    writeSuccess15d1cRegs regs sp /\
  (writeSuccess15d1cAfter regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15d1cObservations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess15d1cObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15d1cLocal tnil (writeSuccess15d1cRegs regs sp), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15d1c), a15d1c.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess15d1cPrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d1cBefore, writeSuccess15d1cLocal,
        writeSuccess15d1cTrace1, writeSuccessTraceTail, a15d1c. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess15d1cTrace1, writeSuccessTraceTail, a15d1c. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d1cTrace2, writeSuccess15d1cTrace1,
        writeSuccessTraceTail, a15d1c. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15d1c). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d1c))
        (value := RVal_Bits (Z_to_bv 64 0x15d1c)).
      - reflexivity.
      - unfold writeSuccess15d1cTrace3, writeSuccess15d1cTrace2,
          writeSuccess15d1cTrace1, writeSuccessTraceTail, a15d1c. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d1cTrace5, writeSuccess15d1cTrace4, writeSuccess15d1cTrace3,
        writeSuccess15d1cTrace2, writeSuccess15d1cTrace1,
        writeSuccess15d1cNextPc, writeSuccessTraceTail, a15d1c. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x15d1c + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d1cTrace5, writeSuccess15d1cTrace4,
        writeSuccess15d1cTrace3, writeSuccess15d1cTrace2,
        writeSuccess15d1cTrace1, writeSuccessTraceTail, a15d1c. cbn.
      apply DeclareConstBitVecS' with (b := sp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits sp) (value := RVal_Bits sp).
      - reflexivity.
      - unfold writeSuccess15d1cTrace6, writeSuccess15d1cTrace5,
          writeSuccess15d1cTrace4, writeSuccess15d1cTrace3,
          writeSuccess15d1cTrace2, writeSuccess15d1cTrace1,
          writeSuccessTraceTail, a15d1c. cbn. constructor.
      - exact Hsp.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d1cTrace7, writeSuccess15d1cTrace6,
        writeSuccess15d1cTrace5, writeSuccess15d1cTrace4,
        writeSuccess15d1cTrace3, writeSuccess15d1cTrace2,
        writeSuccess15d1cTrace1, writeSuccessTraceTail, a15d1c. cbn.
      eapply DefineConstS with (v := Val_Bits (sp + BV 64 0)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX10)
        (value := RVal_Bits (sp + BV 64 0)%bv)
        (updated := RVal_Bits (sp + BV 64 0)%bv).
      - reflexivity.
      - unfold writeSuccess15d1cTrace8, writeSuccess15d1cTrace7,
          writeSuccess15d1cTrace6, writeSuccess15d1cTrace5,
          writeSuccess15d1cTrace4, writeSuccess15d1cTrace3,
          writeSuccess15d1cTrace2, writeSuccess15d1cTrace1,
          writeSuccessTraceTail, a15d1c. cbn. constructor.
      - exact Hx10.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d1c))
        (value := RVal_Bits writeSuccess15d1cNextPc)
        (updated := RVal_Bits writeSuccess15d1cNextPc).
      - reflexivity.
      - unfold writeSuccess15d1cTrace9, writeSuccess15d1cTrace8,
          writeSuccess15d1cTrace7, writeSuccess15d1cTrace6,
          writeSuccess15d1cTrace5, writeSuccess15d1cTrace4,
          writeSuccess15d1cTrace3, writeSuccess15d1cTrace2,
          writeSuccess15d1cTrace1, writeSuccessTraceTail, a15d1c. cbn.
        constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15d20) (trace := a15d20).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x15d20).
      unfold writeSuccess15d1cRegs. rewrite lookup_insert.
      rewrite writeSuccess15d1cNextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15d20), a15d20.
    cbn. unfold writeSuccess15d1cRegs. rewrite lookup_insert.
    rewrite writeSuccess15d1cNextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_15d1c (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d1c)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d1c = Some a15d1c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 ->
  eval_a_exp regs writeSuccess15d1cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d1cBefore regs global)
    (writeSuccess15d1cObservations regs global sp)
    (writeSuccess15d1cAfter regs global sp) /\
  (writeSuccess15d1cAfter regs global sp).1.(seq_regs) =
    writeSuccess15d1cRegs regs sp /\
  (writeSuccess15d1cAfter regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15d1cObservations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  eapply segment_15d1c_mstatus; eauto.
Qed.

Print Assumptions writeSuccess15d1cNextPcExact.
Print Assumptions segment_15d1c_mstatus.
Print Assumptions segment_15d1c.
Print Assumptions writeSuccess15d1cRegsLookupOther.
