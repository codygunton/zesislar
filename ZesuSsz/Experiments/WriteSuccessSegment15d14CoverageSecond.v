From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.

Definition writeSuccess15d14Second5Observations regs global mstatusBits address satp value :=
  firstn 5 (skipn 5 (writeSuccess15d14PrefixObservations regs global
    mstatusBits address satp value false)).

Lemma segment_15d14_second5_covered regs global mstatusBits address satp value
    prefix5 done labels spawned after :
  writeSuccess15d14SysRegs regs ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local writeSuccess15d14Trace5 regs, global)
    prefix5 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists prefix10,
    IslaInstructionPrefixPath
      (writeSuccess15694Local writeSuccess15d14Trace10 regs, global)
      prefix10 done /\
    prefix5 = writeSuccess15d14Second5Observations regs global
      mstatusBits address satp value ++ prefix10.
Proof.
  intros Hsys Hprefix5 Hnil Hdone. destruct Hsys as
    (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
     Hclintbase & Hclintsize & Htohost & Hpriv).
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix5
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l6 & g6 & ? & p6 & Ho5 & Hs5 & ? & Hp6).
  pose (b6 := (l6,g6)).
  eapply writeSuccessAssumeRegCovered in Hs5;
    [|reflexivity|exact Hromsize|reflexivity].
  destruct Hs5 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp6
    ltac:(unfold b6; cbn; discriminate) Hnil HdoneNb) as
    (? & l7 & g7 & ? & p7 & Ho6 & Hs6 & ? & Hp7).
  pose (b7 := (l7,g7)).
  eapply writeSuccessAssumeRegCovered in Hs6;
    [|reflexivity|exact Hclintbase|reflexivity].
  destruct Hs6 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp7
    ltac:(unfold b7; cbn; discriminate) Hnil HdoneNb) as
    (? & l8 & g8 & ? & p8 & Ho7 & Hs7 & ? & Hp8).
  pose (b8 := (l8,g8)).
  eapply writeSuccessAssumeRegCovered in Hs7;
    [|reflexivity|exact Hclintsize|reflexivity].
  destruct Hs7 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp8
    ltac:(unfold b8; cbn; discriminate) Hnil HdoneNb) as
    (? & l9 & g9 & ? & p9 & Ho8 & Hs8 & ? & Hp9).
  pose (b9 := (l9,g9)).
  eapply writeSuccessAssumeRegCovered in Hs8;
    [|reflexivity|exact Htohost|reflexivity].
  destruct Hs8 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp9
    ltac:(unfold b9; cbn; discriminate) Hnil HdoneNb) as
    (? & l10 & g10 & ? & p10 & Ho9 & Hs9 & ? & Hp10).
  pose (b10 := (l10,g10)).
  eapply writeSuccessAssumeRegCovered in Hs9;
    [|reflexivity|exact Hpriv|reflexivity].
  destruct Hs9 as (-> & -> & -> & ->).
  exists p10. split; first exact Hp10.
  unfold writeSuccess15d14Second5Observations,
    writeSuccess15d14PrefixObservations. cbn.
  rewrite Ho5. rewrite Ho6. rewrite Ho7. rewrite Ho8. rewrite Ho9. reflexivity.
Qed.

Print Assumptions segment_15d14_second5_covered.
