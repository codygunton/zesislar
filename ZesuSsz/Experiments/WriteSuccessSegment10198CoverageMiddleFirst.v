From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198CoverageMiddleFirstDeclare.

Definition writeSuccess10198MiddleFirstObservations regs global mstatusBits base :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess10198Trace11 mstatusBits;
     writeSuccess10198Trace12 mstatusBits;
     writeSuccess10198Trace13 mstatusBits base;
     writeSuccess10198Trace14 mstatusBits base;
     writeSuccess10198Trace15 mstatusBits base;
     writeSuccess10198Trace16 mstatusBits base].

Lemma segment_10198_middle_first_covered regs global
    prefix10 done labels spawned after :
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess10198Align = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess10198Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess10198Upper = Some (Val_Bool true) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local writeSuccess10198Trace10 regs, global)
    prefix10 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists (mstatusBits base : bv 64) prefix16,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess10198Trace16 mstatusBits base) regs, global)
      prefix16 done /\
    prefix10 = writeSuccess10198MiddleFirstObservations regs global
      mstatusBits base ++ prefix16.
Proof.
  intros Hmstatus Halign Hlower Hupper Hprefix Hnil Hdone.
  destruct (segment_10198_middle_first_declare_covered regs global
    prefix10 done labels spawned after Hmstatus Hprefix Hnil Hdone) as
    (mstatusBits & base & prefix13 & Hp13 & Hobs13).
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hp13
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l14 & g14 & ? & p14 & Ho13 & Hs13 & ? & Hp14).
  pose (b14 := (l14,g14)). eapply writeSuccessAssumeCovered in Hs13;
    [|reflexivity|exact Halign]. destruct Hs13 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp14
    ltac:(unfold b14; cbn; discriminate) Hnil HdoneNb) as
    (? & l15 & g15 & ? & p15 & Ho14 & Hs14 & ? & Hp15).
  pose (b15 := (l15,g15)). eapply writeSuccessAssumeCovered in Hs14;
    [|reflexivity|exact Hlower]. destruct Hs14 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp15
    ltac:(unfold b15; cbn; discriminate) Hnil HdoneNb) as
    (? & l16 & g16 & ? & p16 & Ho15 & Hs15 & ? & Hp16).
  eapply writeSuccessAssumeCovered in Hs15;
    [|reflexivity|exact Hupper]. destruct Hs15 as (-> & -> & -> & ->).
  exists mstatusBits, base, p16. split; first exact Hp16.
  rewrite Hobs13. unfold writeSuccess10198MiddleFirstObservations,
    writeSuccess10198MiddleFirstDeclareObservations. cbn.
  rewrite Ho13. rewrite Ho14. rewrite Ho15. reflexivity.
Qed.

Print Assumptions segment_10198_middle_first_covered.
