From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.

Definition writeSuccess15d18MiddleFirstObservations regs global mstatusBits address :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess15d18Trace11 mstatusBits;
     writeSuccess15d18Trace12 mstatusBits;
     writeSuccess15d18Trace13 mstatusBits address;
     writeSuccess15d18Trace14 mstatusBits address;
     writeSuccess15d18Trace15 mstatusBits address].

Lemma segment_15d18_middle_first_covered regs global
    prefix10 done labels spawned after :
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d18Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d18Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d18Upper = Some (Val_Bool true) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local writeSuccess15d18Trace10 regs, global)
    prefix10 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists (mstatusBits address : bv 64) prefix15,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess15d18Trace15 mstatusBits address) regs, global)
      prefix15 done /\
    prefix10 = writeSuccess15d18MiddleFirstObservations regs global
      mstatusBits address ++ prefix15.
Proof.
  intros Hmstatus Haligned Hlower Hupper Hprefix Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l11 & g11 & ? & p11 & Ho10 & Hs10 & ? & Hp11).
  pose (b11 := (l11,g11)).
  eapply writeSuccessDeclareConstBitVecCovered in Hs10; [|reflexivity].
  destruct Hs10 as (mstatusBits & -> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp11
    ltac:(unfold b11; cbn; discriminate) Hnil HdoneNb) as
    (? & l12 & g12 & ? & p12 & Ho11 & Hs11 & ? & Hp12).
  pose (b12 := (l12,g12)). eapply writeSuccessAssumeCovered in Hs11;
    [|reflexivity|exact Hmstatus]. destruct Hs11 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp12
    ltac:(unfold b12; cbn; discriminate) Hnil HdoneNb) as
    (? & l13 & g13 & ? & p13 & Ho12 & Hs12 & ? & Hp13).
  pose (b13 := (l13,g13)).
  eapply writeSuccessDeclareConstBitVecCovered in Hs12; [|reflexivity].
  destruct Hs12 as (address & -> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp13
    ltac:(unfold b13; cbn; discriminate) Hnil HdoneNb) as
    (? & l14 & g14 & ? & p14 & Ho13 & Hs13 & ? & Hp14).
  pose (b14 := (l14,g14)). eapply writeSuccessAssumeCovered in Hs13;
    [|reflexivity|exact Haligned]. destruct Hs13 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp14
    ltac:(unfold b14; cbn; discriminate) Hnil HdoneNb) as
    (? & l15 & g15 & ? & p15 & Ho14 & Hs14 & ? & Hp15).
  eapply writeSuccessAssumeCovered in Hs14;
    [|reflexivity|exact Hlower]. destruct Hs14 as (-> & -> & -> & ->).
  exists mstatusBits, address, p15. split; first exact Hp15.
  unfold writeSuccess15d18MiddleFirstObservations. cbn.
  rewrite Ho10. rewrite Ho11. rewrite Ho12. rewrite Ho13. rewrite Ho14.
  reflexivity.
Qed.

Print Assumptions segment_15d18_middle_first_covered.
