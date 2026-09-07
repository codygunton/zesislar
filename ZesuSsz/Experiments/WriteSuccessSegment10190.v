From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a10190.
Require Import IslaTraces.write_success_01.a10194.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess10190Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a10190).
Definition writeSuccess10190Trace2 := writeSuccessTraceTail writeSuccess10190Trace1.
Definition writeSuccess10190Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x10190)) 3
    (writeSuccessTraceTail writeSuccess10190Trace2).
Definition writeSuccess10190Trace4 := writeSuccessTraceTail writeSuccess10190Trace3.
Definition writeSuccess10190NextPc : bv 64 :=
  (Z_to_bv 64 0x10190 + BV 64 4)%bv.
Definition writeSuccess10190Trace5 :=
  subst_trace (Val_Bits writeSuccess10190NextPc) 4
    (writeSuccessTraceTail writeSuccess10190Trace4).
Definition writeSuccess10190Link : bv 64 :=
  (Z_to_bv 64 0x10190 + BV 64 0x2400a000)%bv.
Definition writeSuccess10190Trace6 :=
  subst_trace (Val_Bits writeSuccess10190Link) 5
    (writeSuccessTraceTail writeSuccess10190Trace5).
Definition writeSuccess10190Trace7 := writeSuccessTraceTail writeSuccess10190Trace6.
Definition writeSuccess10190Trace8 := writeSuccessTraceTail writeSuccess10190Trace7.

Definition writeSuccess10190Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess10190NextPc]>
    (<["x5" := RVal_Bits writeSuccess10190Link]> regs).

Lemma writeSuccess10190RegsLookupOther regs reg :
  reg <> "PC" ->
  reg <> "x5" ->
  writeSuccess10190Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx12. unfold writeSuccess10190Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Lemma writeSuccess10190RegsDom regs oldX5 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
  regs !! "x5" = Some oldX5 ->
  dom (writeSuccess10190Regs regs) = dom regs.
Proof.
  intros Hpc Hx12.
  apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx12.
  unfold writeSuccess10190Regs. rewrite !dom_insert_L.
  set_solver.
Qed.

Definition writeSuccess10190Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a10190 regs, global).

Definition writeSuccess10190After (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a10194 (writeSuccess10190Regs regs), global).

Lemma writeSuccess10190NextPcExact :
  writeSuccess10190NextPc = Z_to_bv 64 0x10194.
Proof. unfold writeSuccess10190NextPc. bv_solve. Qed.

Definition writeSuccess10190PrefixObservations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess10190Trace1 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess10190Trace2 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess10190Trace3 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess10190Trace4 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess10190Trace5 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess10190Trace6 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess10190Trace7
       (<["x5" := RVal_Bits writeSuccess10190Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess10190Trace8
       (writeSuccess10190Regs regs)) global].

Definition writeSuccess10190Observations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  writeSuccess10190PrefixObservations regs global ++
  [writeSuccess15694Observation
     (writeSuccess10190After regs global).1 global].

Lemma segment_10190_mstatus (regs : reg_map) (global : seq_global_state) oldX5 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
  regs !! "x5" = Some oldX5 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10194 = Some a10194 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess10190Before regs global)
    (writeSuccess10190Observations regs global)
    (writeSuccess10190After regs global) /\
  (writeSuccess10190After regs global).1.(seq_regs) =
    writeSuccess10190Regs regs /\
  (writeSuccess10190After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess10190Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess10190Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess10190Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x10190), a10190.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess10190PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess10190Before, writeSuccess10190Trace1,
        writeSuccessTraceTail, a10190. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess10190Trace1, writeSuccessTraceTail, a10190. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess10190Trace2, writeSuccess10190Trace1,
        writeSuccessTraceTail, a10190. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x10190). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x10190))
        (value := RVal_Bits (Z_to_bv 64 0x10190)).
      - reflexivity.
      - unfold writeSuccess10190Trace3, writeSuccess10190Trace2,
          writeSuccess10190Trace1, writeSuccessTraceTail, a10190. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess10190Trace5, writeSuccess10190Trace4,
        writeSuccess10190Trace3, writeSuccess10190Trace2,
        writeSuccess10190Trace1, writeSuccess10190NextPc,
        writeSuccessTraceTail, a10190. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x10190 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess10190Trace5, writeSuccess10190Trace4,
        writeSuccess10190Trace3, writeSuccess10190Trace2,
        writeSuccess10190Trace1, writeSuccess10190Link,
        writeSuccessTraceTail, a10190. cbn.
      eapply DefineConstS with
        (v := Val_Bits
          (Z_to_bv 64 0x10190 + BV 64 0x2400a000)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX5)
        (value := RVal_Bits writeSuccess10190Link)
        (updated := RVal_Bits writeSuccess10190Link).
      - reflexivity.
      - unfold writeSuccess10190Trace6, writeSuccess10190Trace5,
          writeSuccess10190Link, writeSuccess10190Trace4,
          writeSuccess10190Trace3, writeSuccess10190Trace2,
          writeSuccess10190Trace1, writeSuccessTraceTail, a10190. cbn.
        constructor.
      - exact Hx12.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x10190))
        (value := RVal_Bits writeSuccess10190NextPc)
        (updated := RVal_Bits writeSuccess10190NextPc).
      - reflexivity.
      - unfold writeSuccess10190Trace7, writeSuccess10190Trace6,
          writeSuccess10190Trace5,
          writeSuccess10190Trace4, writeSuccess10190Trace3,
          writeSuccess10190Trace2, writeSuccess10190Trace1,
          writeSuccessTraceTail, a10190. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a10194) (trace := a10194).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x10194).
      unfold writeSuccess10190Regs. rewrite lookup_insert.
      rewrite writeSuccess10190NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x10194), a10194.
    cbn. unfold writeSuccess10190Regs. rewrite lookup_insert.
    rewrite writeSuccess10190NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_10190 (regs : reg_map) (global : seq_global_state) oldX5 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
  regs !! "x5" = Some oldX5 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10194 = Some a10194 ->
  writeSuccessTraceAssumptions (writeSuccess10190Before regs global) ->
  IslaInstructionSegment (writeSuccess10190Before regs global)
    (writeSuccess10190Observations regs global)
    (writeSuccess10190After regs global) /\
  (writeSuccess10190After regs global).1.(seq_regs) =
    writeSuccess10190Regs regs /\
  (writeSuccess10190After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess10190Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hassumptions.
  eapply segment_10190_mstatus; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions
    regs global Hassumptions).
Qed.

Print Assumptions segment_10190_mstatus.
Print Assumptions segment_10190.
Print Assumptions writeSuccess10190RegsLookupOther.
Print Assumptions writeSuccess10190RegsDom.
