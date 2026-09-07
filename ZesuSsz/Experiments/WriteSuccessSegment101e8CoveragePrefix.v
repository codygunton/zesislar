From Coq Require Import Eqdep_dec.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101e8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e8.

Definition writeSuccess101e8First7Observations regs global left :=
  firstn 7 (writeSuccess101e8PrefixObservations regs global left (BV 64 0)).

Ltac unfold_101e8 H :=
  cbn [writeSuccess101e8Before writeSuccess101e8Trace1
    writeSuccess101e8Trace2 writeSuccess101e8Trace3 writeSuccess101e8Trace4
    writeSuccess101e8Trace5 writeSuccess101e8Trace6 writeSuccess101e8Trace7
    writeSuccess101e8NextPc writeSuccessTraceTail a101e8] in H.

Lemma segment_101e8_prefix7_covered regs global (left : bv 64)
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e8)) ->
  regs !! "x10" = Some (RVal_Bits left) ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101e8Before regs global)
    observations after ->
  exists done labels spawned prefix7,
    IslaInstructionPrefixPath
      (writeSuccess15694Local (writeSuccess101e8Trace7 left) regs, global)
      prefix7 done /\
    done.1.(seq_trace) = tnil /\
    seq_step done.1 done.2 labels after.1 after.2 spawned /\
    (IslaInstructionBoundary after \/ IslaInstructionTrap after) /\
    observations = writeSuccess101e8First7Observations regs global left ++
      prefix7 ++ ({| microLabels := labels; microAfter := after |} :: []).
Proof.
  intros Hpc Hleft Hmstatus Hsegment.
  destruct Hsegment as [Hstart done prefix labels spawned Hprefix Hnil Hdone Hobs Hend].
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(unfold writeSuccess101e8Before, writeSuccess15694Local, a101e8;
      discriminate) Hnil HdoneNb) as
    (? & l1 & g1 & ? & p1 & Ho0 & Hs0 & ? & Hp1).
  pose (b1 := (l1,g1)). inversion Hs0 as [? ? ? ? ? ? ? ? Ht0 Hsem0]; subst.
  unfold_101e8 Ht0. inversion Ht0; subst. cbn in Hsem0.
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
  unfold b2 in Ht2. unfold_101e8 Ht2. inversion Ht2; subst. cbn in Hsem2.
  destruct Hsem2 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp3
    ltac:(unfold b3; cbn; discriminate) Hnil HdoneNb) as
    (? & l4 & g4 & ? & p4 & Ho3 & Hs3 & Hnb4 & Hp4).
  eapply writeSuccessReadRegCovered in Hs3.
  2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: exact Hnb4.
  destruct Hs3 as (-> & -> & -> & -> & HsymPc).
  cbn in HsymPc. inversion HsymPc as [HpcVal].
  assert (HpcBits : @BV 64 n0 Heq0 = Z_to_bv 64 0x101e8).
  { apply bv_eq. cbn. exact HpcVal. }
  repeat match goal with H : context [@BV 64 n0 Heq0] |- _ => rewrite HpcBits in H end.
  destruct (writeSuccess15694TakeStep _ _ _ Hp4
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l5 & g5 & ? & p5 & Ho4 & Hs4 & ? & Hp5).
  eapply writeSuccessDefineConstCovered in Hs4; [|reflexivity|reflexivity].
  destruct Hs4 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp5
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l6 & g6 & ? & p6 & Ho5 & Hs5 & ? & Hp6).
  pose (b6 := (l6,g6)). inversion Hs5 as [? ? ? ? ? ? ? ? Ht5 Hsem5]; subst.
  unfold b6 in Ht5. unfold_101e8 Ht5. inversion Ht5; subst. cbn in Hsem5.
  destruct Hsem5 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp6
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l7 & g7 & ? & p7 & Ho6 & Hs6 & Hnb7 & Hp7).
  eapply writeSuccessReadRegCovered in Hs6.
  2: reflexivity. 2: exact Hleft. 2: reflexivity. 2: exact Hnb7.
  destruct Hs6 as (-> & -> & -> & -> & HsymLeft).
  cbn in HsymLeft. inversion HsymLeft as [HleftVal].
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    (@BV 64 n0 Heq1) left HleftVal) as HleftBits.
  repeat match goal with H : context [@BV 64 n0 Heq1] |- _ => rewrite HleftBits in H end.
  exists done, labels, spawned, p7.
  split; first exact Hp7. split; first exact Hnil.
  split; first exact Hdone. split; first exact Hend.
  unfold writeSuccess101e8First7Observations,
    writeSuccess101e8PrefixObservations, writeSuccess101e8Locals. cbn.
  rewrite Ho6. rewrite HpcBits. rewrite HleftBits. reflexivity.
Qed.

Print Assumptions segment_101e8_prefix7_covered.
