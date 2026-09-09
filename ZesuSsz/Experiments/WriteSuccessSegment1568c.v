From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_89.a1568c.
Require Import IslaTraces.write_success_89.a15690.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessTraceTail (trace : isla_trace) : isla_trace :=
  match trace with tcons _ rest => rest | _ => tnil end.

Definition writeSuccess1568cMstatus : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccess1568cTrace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a1568c).
Definition writeSuccess1568cTrace2 := writeSuccessTraceTail writeSuccess1568cTrace1.
Definition writeSuccess1568cTrace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x1568c)) 3
    (writeSuccessTraceTail writeSuccess1568cTrace2).
Definition writeSuccess1568cTrace4 := writeSuccessTraceTail writeSuccess1568cTrace3.
Definition writeSuccess1568cNextPc : bv 64 :=
  (Z_to_bv 64 0x1568c + BV 64 4)%bv.
Definition writeSuccess1568cTrace5 :=
  subst_trace (Val_Bits writeSuccess1568cNextPc) 4
    (writeSuccessTraceTail writeSuccess1568cTrace4).
Definition writeSuccess1568cTrace6 (sp : bv 64) :=
  subst_trace (Val_Bits sp) 5 (writeSuccessTraceTail writeSuccess1568cTrace5).
Definition writeSuccess1568cTrace7 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess1568cTrace6 sp).
Definition writeSuccess1568cTrace8 (sp : bv 64) :=
  subst_trace (Val_Bits (sp + BV 64 1768)%bv) 6
    (writeSuccessTraceTail (writeSuccess1568cTrace7 sp)).
Definition writeSuccess1568cTrace9 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess1568cTrace8 sp).
Definition writeSuccess1568cTrace10 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess1568cTrace9 sp).

Definition writeSuccess1568cRegs (regs : reg_map) (sp : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess1568cNextPc]>
    (<["x18" := RVal_Bits (sp + BV 64 1768)%bv]> regs).

Lemma writeSuccess1568cRegsLookupOther regs sp reg :
  reg <> "PC" ->
  reg <> "x18" ->
  writeSuccess1568cRegs regs sp !! reg = regs !! reg.
Proof.
  intros Hpc Hx10. unfold writeSuccess1568cRegs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Definition writeSuccess1568cLocal (trace : isla_trace) (regs : reg_map) :
    seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccess1568cBefore (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess1568cLocal a1568c regs, global).

Definition writeSuccess1568cAfter (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) : IslaState :=
  (writeSuccess1568cLocal a15690 (writeSuccess1568cRegs regs sp), global).

Definition writeSuccess1568cObservation (local : seq_local_state)
    (global : seq_global_state) : IslaMicroObservation := {|
  microLabels := [];
  microAfter := (local, global)
|}.

Lemma writeSuccess1568cNextPcExact :
  writeSuccess1568cNextPc = Z_to_bv 64 0x15690.
Proof. unfold writeSuccess1568cNextPc. bv_solve. Qed.

Definition writeSuccess1568cPrefixObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  [writeSuccess1568cObservation
     (writeSuccess1568cLocal writeSuccess1568cTrace1 regs) global;
   writeSuccess1568cObservation
     (writeSuccess1568cLocal writeSuccess1568cTrace2 regs) global;
   writeSuccess1568cObservation
     (writeSuccess1568cLocal writeSuccess1568cTrace3 regs) global;
   writeSuccess1568cObservation
     (writeSuccess1568cLocal writeSuccess1568cTrace4 regs) global;
   writeSuccess1568cObservation
     (writeSuccess1568cLocal writeSuccess1568cTrace5 regs) global;
   writeSuccess1568cObservation
     (writeSuccess1568cLocal (writeSuccess1568cTrace6 sp) regs) global;
   writeSuccess1568cObservation
     (writeSuccess1568cLocal (writeSuccess1568cTrace7 sp) regs) global;
   writeSuccess1568cObservation
     (writeSuccess1568cLocal (writeSuccess1568cTrace8 sp) regs) global;
   writeSuccess1568cObservation
     (writeSuccess1568cLocal (writeSuccess1568cTrace9 sp)
       (<["x18" := RVal_Bits (sp + BV 64 1768)%bv]> regs)) global;
   writeSuccess1568cObservation
     (writeSuccess1568cLocal (writeSuccess1568cTrace10 sp)
       (writeSuccess1568cRegs regs sp)) global].

Definition writeSuccess1568cObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  writeSuccess1568cPrefixObservations regs global sp ++
  [writeSuccess1568cObservation
     (writeSuccess1568cAfter regs global sp).1 global].

Lemma writeSuccess1568cTakeStep before observations done :
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

Lemma segment_1568c_mstatus (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX18 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1568c)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x18" = Some oldX18 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1568c = Some a1568c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15690 = Some a15690 ->
  eval_a_exp regs writeSuccess1568cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess1568cBefore regs global)
    (writeSuccess1568cObservations regs global sp)
    (writeSuccess1568cAfter regs global sp) /\
  (writeSuccess1568cAfter regs global sp).1.(seq_regs) =
    writeSuccess1568cRegs regs sp /\
  (writeSuccess1568cAfter regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess1568cObservations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess1568cObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess1568cLocal tnil (writeSuccess1568cRegs regs sp), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x1568c), a1568c.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess1568cPrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1568cBefore, writeSuccess1568cLocal,
        writeSuccess1568cTrace1, writeSuccessTraceTail, a1568c. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess1568cTrace1, writeSuccessTraceTail, a1568c. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1568cTrace2, writeSuccess1568cTrace1,
        writeSuccessTraceTail, a1568c. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x1568c). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x1568c))
        (value := RVal_Bits (Z_to_bv 64 0x1568c)).
      - reflexivity.
      - unfold writeSuccess1568cTrace3, writeSuccess1568cTrace2,
          writeSuccess1568cTrace1, writeSuccessTraceTail, a1568c. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1568cTrace5, writeSuccess1568cTrace4, writeSuccess1568cTrace3,
        writeSuccess1568cTrace2, writeSuccess1568cTrace1,
        writeSuccess1568cNextPc, writeSuccessTraceTail, a1568c. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x1568c + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1568cTrace5, writeSuccess1568cTrace4,
        writeSuccess1568cTrace3, writeSuccess1568cTrace2,
        writeSuccess1568cTrace1, writeSuccessTraceTail, a1568c. cbn.
      apply DeclareConstBitVecS' with (b := sp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits sp) (value := RVal_Bits sp).
      - reflexivity.
      - unfold writeSuccess1568cTrace6, writeSuccess1568cTrace5,
          writeSuccess1568cTrace4, writeSuccess1568cTrace3,
          writeSuccess1568cTrace2, writeSuccess1568cTrace1,
          writeSuccessTraceTail, a1568c. cbn. constructor.
      - exact Hsp.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1568cTrace7, writeSuccess1568cTrace6,
        writeSuccess1568cTrace5, writeSuccess1568cTrace4,
        writeSuccess1568cTrace3, writeSuccess1568cTrace2,
        writeSuccess1568cTrace1, writeSuccessTraceTail, a1568c. cbn.
      eapply DefineConstS with (v := Val_Bits (sp + BV 64 1768)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX18)
        (value := RVal_Bits (sp + BV 64 1768)%bv)
        (updated := RVal_Bits (sp + BV 64 1768)%bv).
      - reflexivity.
      - unfold writeSuccess1568cTrace8, writeSuccess1568cTrace7,
          writeSuccess1568cTrace6, writeSuccess1568cTrace5,
          writeSuccess1568cTrace4, writeSuccess1568cTrace3,
          writeSuccess1568cTrace2, writeSuccess1568cTrace1,
          writeSuccessTraceTail, a1568c. cbn. constructor.
      - exact Hx10.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x1568c))
        (value := RVal_Bits writeSuccess1568cNextPc)
        (updated := RVal_Bits writeSuccess1568cNextPc).
      - reflexivity.
      - unfold writeSuccess1568cTrace9, writeSuccess1568cTrace8,
          writeSuccess1568cTrace7, writeSuccess1568cTrace6,
          writeSuccess1568cTrace5, writeSuccess1568cTrace4,
          writeSuccess1568cTrace3, writeSuccess1568cTrace2,
          writeSuccess1568cTrace1, writeSuccessTraceTail, a1568c. cbn.
        constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15690) (trace := a15690).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x15690).
      unfold writeSuccess1568cRegs. rewrite lookup_insert.
      rewrite writeSuccess1568cNextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15690), a15690.
    cbn. unfold writeSuccess1568cRegs. rewrite lookup_insert.
    rewrite writeSuccess1568cNextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_1568c (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX18 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1568c)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x18" = Some oldX18 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1568c = Some a1568c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15690 = Some a15690 ->
  eval_a_exp regs writeSuccess1568cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess1568cBefore regs global)
    (writeSuccess1568cObservations regs global sp)
    (writeSuccess1568cAfter regs global sp) /\
  (writeSuccess1568cAfter regs global sp).1.(seq_regs) =
    writeSuccess1568cRegs regs sp /\
  (writeSuccess1568cAfter regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess1568cObservations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  eapply segment_1568c_mstatus; eauto.
Qed.

Print Assumptions writeSuccess1568cNextPcExact.
Print Assumptions segment_1568c_mstatus.
Print Assumptions segment_1568c.
Print Assumptions writeSuccess1568cRegsLookupOther.
