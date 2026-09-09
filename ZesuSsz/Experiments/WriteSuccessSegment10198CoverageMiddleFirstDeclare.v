From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.

Definition writeSuccess10198MiddleFirstDeclareObservations regs global
    mstatusBits base :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess10198Trace11 mstatusBits;
     writeSuccess10198Trace12 mstatusBits;
     writeSuccess10198Trace13 mstatusBits base].

Lemma segment_10198_middle_first_declare_covered regs global
    prefix10 done labels spawned after :
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local writeSuccess10198Trace10 regs, global)
    prefix10 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists (mstatusBits base : bv 64) prefix13,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess10198Trace13 mstatusBits base) regs, global)
      prefix13 done /\
    prefix10 = writeSuccess10198MiddleFirstDeclareObservations regs global
      mstatusBits base ++ prefix13.
Proof.
  intros Hmstatus Hprefix Hnil Hdone.
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
  eapply writeSuccessDeclareConstBitVecCovered in Hs12; [|reflexivity].
  destruct Hs12 as (base & -> & -> & -> & ->).
  exists mstatusBits, base, p13. split; first exact Hp13.
  unfold writeSuccess10198MiddleFirstDeclareObservations. cbn.
  rewrite Ho10. rewrite Ho11. rewrite Ho12. reflexivity.
Qed.

Print Assumptions segment_10198_middle_first_declare_covered.
