Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156ac.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ac.

Definition writeSuccess156acFirst5Observations regs global :=
  firstn 5 (writeSuccess156acPrefixObservations regs global).

Ltac unfold_156ac_prefix H :=
  cbn [writeSuccess156acBefore writeSuccess15694Local
    writeSuccess156acTrace1 writeSuccess156acTrace2
    writeSuccess156acTrace3 writeSuccess156acTrace4
    writeSuccess156acTrace5 writeSuccess156acNextPc
    writeSuccessTraceTail a156ac] in H.

Lemma segment_156ac_prefix5_covered regs global
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156ac)) ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156acBefore regs global)
    observations after ->
  exists done labels spawned prefix5,
    IslaInstructionPrefixPath
      (writeSuccess15694Local writeSuccess156acTrace5 regs, global)
      prefix5 done /\
    done.1.(seq_trace) = tnil /\
    seq_step done.1 done.2 labels after.1 after.2 spawned /\
    (IslaInstructionBoundary after \/ IslaInstructionTrap after) /\
    observations = writeSuccess156acFirst5Observations regs global ++
      prefix5 ++ ({| microLabels := labels; microAfter := after |} :: []).
Proof.
  intros Hpc Hmstatus Hsegment.
  destruct Hsegment as [Hstart done prefix labels spawned Hprefix Hnil Hdone Hobs Hend].
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(unfold writeSuccess156acBefore, writeSuccess15694Local, a156ac;
      discriminate) Hnil HdoneNb) as
    (? & l1 & g1 & ? & p1 & Ho0 & Hs0 & ? & Hp1).
  pose (b1 := (l1,g1)). inversion Hs0 as [? ? ? ? ? ? ? ? Ht0 Hsem0]; subst.
  unfold_156ac_prefix Ht0. inversion Ht0; subst. cbn in Hsem0.
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
  unfold b2 in Ht2. unfold_156ac_prefix Ht2. inversion Ht2; subst.
  cbn in Hsem2. destruct Hsem2 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp3
    ltac:(unfold b3; cbn; discriminate) Hnil HdoneNb) as
    (? & l4 & g4 & ? & p4 & Ho3 & Hs3 & Hnb4 & Hp4).
  eapply writeSuccessReadRegCovered in Hs3.
  2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: exact Hnb4.
  destruct Hs3 as (-> & -> & -> & -> & HsymPc).
  cbn in HsymPc. inversion HsymPc as [HpcVal].
  assert (HpcBits : @BV 64 n0 Heq0 = Z_to_bv 64 0x156ac).
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
  unfold writeSuccess156acFirst5Observations,
    writeSuccess156acPrefixObservations. cbn.
  rewrite Ho3. rewrite Ho4. rewrite HpcBits. reflexivity.
Qed.

Print Assumptions segment_156ac_prefix5_covered.
