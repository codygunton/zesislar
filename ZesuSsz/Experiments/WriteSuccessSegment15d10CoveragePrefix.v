From Coq Require Import Eqdep_dec.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.

Definition writeSuccess15d10First5Observations regs global sp :=
  firstn 5 (writeSuccess15d10PrefixObservations regs global sp).

Ltac unfold_15d10_prefix H :=
  cbn [writeSuccess15d10Before writeSuccess15d10Local
    writeSuccess15d10Trace1 writeSuccess15d10Trace2
    writeSuccess15d10Trace3 writeSuccess15d10Trace4
    writeSuccess15d10Trace5 writeSuccess15d10NextPc
    writeSuccessTraceTail a15d10] in H.

Lemma segment_15d10_prefix5_covered regs global (sp : bv 64)
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  eval_a_exp regs writeSuccess15d10Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d10Before regs global)
    observations after ->
  exists done labels spawned prefix5,
    IslaInstructionPrefixPath
      (writeSuccess15d10Local writeSuccess15d10Trace5 regs, global)
      prefix5 done /\
    done.1.(seq_trace) = tnil /\
    seq_step done.1 done.2 labels after.1 after.2 spawned /\
    (IslaInstructionBoundary after \/ IslaInstructionTrap after) /\
    observations = writeSuccess15d10First5Observations regs global sp ++
      prefix5 ++ ({| microLabels := labels; microAfter := after |} :: []).
Proof.
  intros Hpc Hmstatus Hsegment.
  destruct Hsegment as [Hstart done prefix labels spawned Hprefix Hnil Hdone Hobs Hend].
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(unfold writeSuccess15d10Before, writeSuccess15d10Local, a15d10;
      discriminate) Hnil HdoneNb) as
    (? & l1 & g1 & ? & p1 & Ho0 & Hs0 & ? & Hp1).
  pose (b1 := (l1,g1)). inversion Hs0 as [? ? ? ? ? ? ? ? Ht0 Hsem0]; subst.
  unfold_15d10_prefix Ht0. inversion Ht0; subst. cbn in Hsem0.
  destruct Hsem0 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp1
    ltac:(unfold b1; cbn; discriminate) Hnil HdoneNb) as
    (? & l2 & g2 & ? & p2 & Ho1 & Hs1 & ? & Hp2).
  pose (b2 := (l2,g2)). eapply writeSuccessAssumeCovered in Hs1;
    [|reflexivity|exact Hmstatus]. destruct Hs1 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp2
    ltac:(unfold b2; cbn; discriminate) Hnil HdoneNb) as
    (? & l3 & g3 & ? & p3 & Ho2 & Hs2 & ? & Hp3).
  pose (b3 := (l3,g3)). inversion Hs2 as [? ? ? ? ? ? ? ? Ht2 Hsem2]; subst.
  unfold b2 in Ht2. unfold_15d10_prefix Ht2. inversion Ht2; subst.
  cbn in Hsem2. destruct Hsem2 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp3
    ltac:(unfold b3; cbn; discriminate) Hnil HdoneNb) as
    (? & l4 & g4 & ? & p4 & Ho3 & Hs3 & Hnb4 & Hp4).
  eapply writeSuccessReadRegCovered in Hs3.
  2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: exact Hnb4.
  destruct Hs3 as (-> & -> & -> & -> & HsymPc).
  cbn in HsymPc. inversion HsymPc as [HpcVal].
  assert (HpcBits : @BV 64 n0 Heq0 = Z_to_bv 64 0x15d10).
  { apply bv_eq. cbn. exact HpcVal. }
  repeat match goal with H : context [@BV 64 n0 Heq0] |- _ =>
    rewrite HpcBits in H end.
  destruct (writeSuccess15694TakeStep _ _ _ Hp4
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l5 & g5 & ? & p5 & Ho4 & Hs4 & ? & Hp5).
  eapply writeSuccessDefineConstCovered in Hs4; [|reflexivity|reflexivity].
  destruct Hs4 as (-> & -> & -> & ->).
  exists done, labels, spawned, p5.
  split; first exact Hp5. split; first exact Hnil.
  split; first exact Hdone. split; first exact Hend.
  unfold writeSuccess15d10First5Observations,
    writeSuccess15d10PrefixObservations. cbn.
  rewrite Ho3. rewrite Ho4. rewrite HpcBits. reflexivity.
Qed.

Print Assumptions segment_15d10_prefix5_covered.
