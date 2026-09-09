From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a1019c.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.

Definition writeSuccess1019cFirst5Observations regs global mstatusBits address satp value :=
  firstn 5 (writeSuccess1019cPrefixObservations regs global
    mstatusBits address satp value false WriteSuccessStoreBacked).

Lemma segment_1019c_prefix5_covered regs global mstatusBits address satp value
    observations after :
  writeSuccess1019cSysRegs regs ->
  IslaInstructionSegment (writeSuccess1019cBefore regs global) observations after ->
  exists done labels spawned prefix5,
    IslaInstructionPrefixPath
      (writeSuccess15694Local writeSuccess1019cTrace5 regs, global)
      prefix5 done /\
    done.1.(seq_trace) = tnil /\
    seq_step done.1 done.2 labels after.1 after.2 spawned /\
    (IslaInstructionBoundary after \/ IslaInstructionTrap after) /\
    observations = writeSuccess1019cFirst5Observations regs global
      mstatusBits address satp value ++ prefix5 ++
      ({| microLabels := labels; microAfter := after |} :: []).
Proof.
  intros Hsys Hsegment. destruct Hsys as
    (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
     Hclintbase & Hclintsize & Htohost & Hpriv).
  destruct Hsegment as [Hstart done prefix labels spawned Hprefix Hnil Hdone Hobs Hend].
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(unfold writeSuccess1019cBefore, writeSuccess15694Local, a1019c; discriminate) Hnil HdoneNb) as
    (? & l1 & g1 & ? & p1 & Ho0 & Hs0 & ? & Hp1).
  pose (b1 := (l1,g1)).
  eapply writeSuccessAssumeRegCovered in Hs0;
    [|reflexivity|exact Hpmp|reflexivity].
  destruct Hs0 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp1
    ltac:(unfold b1; cbn; discriminate) Hnil HdoneNb) as
    (? & l2 & g2 & ? & p2 & Ho1 & Hs1 & ? & Hp2).
  pose (b2 := (l2,g2)).
  eapply writeSuccessAssumeRegCovered in Hs1;
    [|reflexivity|exact Hmisaligned|reflexivity].
  destruct Hs1 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp2
    ltac:(unfold b2; cbn; discriminate) Hnil HdoneNb) as
    (? & l3 & g3 & ? & p3 & Ho2 & Hs2 & ? & Hp3).
  pose (b3 := (l3,g3)).
  eapply writeSuccessAssumeRegCovered in Hs2;
    [|reflexivity|exact Hrambase|reflexivity].
  destruct Hs2 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp3
    ltac:(unfold b3; cbn; discriminate) Hnil HdoneNb) as
    (? & l4 & g4 & ? & p4 & Ho3 & Hs3 & ? & Hp4).
  pose (b4 := (l4,g4)).
  eapply writeSuccessAssumeRegCovered in Hs3;
    [|reflexivity|exact Hramsize|reflexivity].
  destruct Hs3 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp4
    ltac:(unfold b4; cbn; discriminate) Hnil HdoneNb) as
    (? & l5 & g5 & ? & p5 & Ho4 & Hs4 & ? & Hp5).
  pose (b5 := (l5,g5)).
  eapply writeSuccessAssumeRegCovered in Hs4;
    [|reflexivity|exact Hrombase|reflexivity].
  destruct Hs4 as (-> & -> & -> & ->).
  exists done, labels, spawned, p5.
  split; first exact Hp5. split; first exact Hnil.
  split; first exact Hdone. split; first exact Hend.
  unfold writeSuccess1019cFirst5Observations,
    writeSuccess1019cPrefixObservations. cbn.
  rewrite Hobs. rewrite Ho0. rewrite Ho1. rewrite Ho2. rewrite Ho3. rewrite Ho4.
  reflexivity.
Qed.

Print Assumptions segment_1019c_prefix5_covered.
