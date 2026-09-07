From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156ac.
Require Import IslaTraces.write_success_91.a156b0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156acTrace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156ac).
Definition writeSuccess156acTrace2 := writeSuccessTraceTail writeSuccess156acTrace1.
Definition writeSuccess156acTrace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156ac)) 3
    (writeSuccessTraceTail writeSuccess156acTrace2).
Definition writeSuccess156acTrace4 := writeSuccessTraceTail writeSuccess156acTrace3.
Definition writeSuccess156acNextPc : bv 64 :=
  (Z_to_bv 64 0x156ac + BV 64 4)%bv.
Definition writeSuccess156acTrace5 :=
  subst_trace (Val_Bits writeSuccess156acNextPc) 4
    (writeSuccessTraceTail writeSuccess156acTrace4).
Definition writeSuccess156acLink : bv 64 :=
  (Z_to_bv 64 0x156ac + BV 64 0x0)%bv.
Definition writeSuccess156acTrace6 :=
  subst_trace (Val_Bits writeSuccess156acLink) 5
    (writeSuccessTraceTail writeSuccess156acTrace5).
Definition writeSuccess156acTrace7 := writeSuccessTraceTail writeSuccess156acTrace6.
Definition writeSuccess156acTrace8 := writeSuccessTraceTail writeSuccess156acTrace7.

Definition writeSuccess156acRegs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156acNextPc]>
    (<["x1" := RVal_Bits writeSuccess156acLink]> regs).

Lemma writeSuccess156acRegsLookupOther regs reg :
  reg <> "PC" ->
  reg <> "x1" ->
  writeSuccess156acRegs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx12. unfold writeSuccess156acRegs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Lemma writeSuccess156acRegsDom regs oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156ac)) ->
  regs !! "x1" = Some oldX1 ->
  dom (writeSuccess156acRegs regs) = dom regs.
Proof.
  intros Hpc Hx12.
  apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx12.
  unfold writeSuccess156acRegs. rewrite !dom_insert_L.
  set_solver.
Qed.

Definition writeSuccess156acBefore (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156ac regs, global).

Definition writeSuccess156acAfter (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156b0 (writeSuccess156acRegs regs), global).

Lemma writeSuccess156acNextPcExact :
  writeSuccess156acNextPc = Z_to_bv 64 0x156b0.
Proof. unfold writeSuccess156acNextPc. bv_solve. Qed.

Definition writeSuccess156acPrefixObservations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156acTrace1 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156acTrace2 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156acTrace3 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156acTrace4 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156acTrace5 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156acTrace6 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156acTrace7
       (<["x1" := RVal_Bits writeSuccess156acLink]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156acTrace8
       (writeSuccess156acRegs regs)) global].

Definition writeSuccess156acObservations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  writeSuccess156acPrefixObservations regs global ++
  [writeSuccess15694Observation
     (writeSuccess156acAfter regs global).1 global].

Lemma segment_156ac_mstatus (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156ac)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156acBefore regs global)
    (writeSuccess156acObservations regs global)
    (writeSuccess156acAfter regs global) /\
  (writeSuccess156acAfter regs global).1.(seq_regs) =
    writeSuccess156acRegs regs /\
  (writeSuccess156acAfter regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156acObservations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156acObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156acRegs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156ac), a156ac.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156acPrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156acBefore, writeSuccess156acTrace1,
        writeSuccessTraceTail, a156ac. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess156acTrace1, writeSuccessTraceTail, a156ac. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156acTrace2, writeSuccess156acTrace1,
        writeSuccessTraceTail, a156ac. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156ac). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x156ac))
        (value := RVal_Bits (Z_to_bv 64 0x156ac)).
      - reflexivity.
      - unfold writeSuccess156acTrace3, writeSuccess156acTrace2,
          writeSuccess156acTrace1, writeSuccessTraceTail, a156ac. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156acTrace5, writeSuccess156acTrace4,
        writeSuccess156acTrace3, writeSuccess156acTrace2,
        writeSuccess156acTrace1, writeSuccess156acNextPc,
        writeSuccessTraceTail, a156ac. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x156ac + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156acTrace5, writeSuccess156acTrace4,
        writeSuccess156acTrace3, writeSuccess156acTrace2,
        writeSuccess156acTrace1, writeSuccess156acLink,
        writeSuccessTraceTail, a156ac. cbn.
      eapply DefineConstS with
        (v := Val_Bits
          (Z_to_bv 64 0x156ac + BV 64 0x0)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX1)
        (value := RVal_Bits writeSuccess156acLink)
        (updated := RVal_Bits writeSuccess156acLink).
      - reflexivity.
      - unfold writeSuccess156acTrace6, writeSuccess156acTrace5,
          writeSuccess156acLink, writeSuccess156acTrace4,
          writeSuccess156acTrace3, writeSuccess156acTrace2,
          writeSuccess156acTrace1, writeSuccessTraceTail, a156ac. cbn.
        constructor.
      - exact Hx12.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x156ac))
        (value := RVal_Bits writeSuccess156acNextPc)
        (updated := RVal_Bits writeSuccess156acNextPc).
      - reflexivity.
      - unfold writeSuccess156acTrace7, writeSuccess156acTrace6,
          writeSuccess156acTrace5,
          writeSuccess156acTrace4, writeSuccess156acTrace3,
          writeSuccess156acTrace2, writeSuccess156acTrace1,
          writeSuccessTraceTail, a156ac. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156b0) (trace := a156b0).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x156b0).
      unfold writeSuccess156acRegs. rewrite lookup_insert.
      rewrite writeSuccess156acNextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156b0), a156b0.
    cbn. unfold writeSuccess156acRegs. rewrite lookup_insert.
    rewrite writeSuccess156acNextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_156ac (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156ac)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  writeSuccessTraceAssumptions (writeSuccess156acBefore regs global) ->
  IslaInstructionSegment (writeSuccess156acBefore regs global)
    (writeSuccess156acObservations regs global)
    (writeSuccess156acAfter regs global) /\
  (writeSuccess156acAfter regs global).1.(seq_regs) =
    writeSuccess156acRegs regs /\
  (writeSuccess156acAfter regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156acObservations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hassumptions.
  eapply segment_156ac_mstatus; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions
    regs global Hassumptions).
Qed.

Print Assumptions segment_156ac_mstatus.
Print Assumptions segment_156ac.
Print Assumptions writeSuccess156acRegsLookupOther.
Print Assumptions writeSuccess156acRegsDom.
