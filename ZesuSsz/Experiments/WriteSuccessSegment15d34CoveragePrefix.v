(* Generated from the pinned return trace shape. *)
From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d34.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.

Import ListNotations.

Ltac unfold_write_success_15d34_trace H :=
  cbn [writeSuccess15d34Before writeSuccess15d34Trace1
    writeSuccess15d34Trace2 writeSuccess15d34Trace3
    writeSuccess15d34Trace4 writeSuccess15d34Trace5
    writeSuccess15d34Trace6 writeSuccess15d34Trace7
    writeSuccess15d34Trace8 writeSuccessTraceTail a15d34] in H.

Lemma segment_15d34_prefix8_covered regs global (ra : bv 64)
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d34)) ->
  regs !! "x1" = Some (RVal_Bits ra) ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d34Alignment = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d34Before regs global)
    observations after ->
  exists done labels spawned prefix8,
    IslaInstructionPrefixPath
      (writeSuccess15694Local (writeSuccess15d34Trace8 ra) regs, global)
      prefix8 done /\
    done.1.(seq_trace) = tnil /\
    seq_step done.1 done.2 labels after.1 after.2 spawned /\
    (IslaInstructionBoundary after \/ IslaInstructionTrap after) /\
    observations = writeSuccess15d34Prefix8Observations regs global ra ++
      prefix8 ++ ({| microLabels := labels; microAfter := after |} :: []).
Proof.
  intros Hpc Hx1 Hmstatus Halign Hsegment.
  destruct Hsegment as
    [Hstart done prefix labels spawned Hprefix Hnil Hdone Hobservations Hend].
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(unfold writeSuccess15d34Before, writeSuccess15694Local,
      a15d34; discriminate) Hnil HdoneNb) as
    (? & local1 & global1 & ? & prefix1 & Hobs0 & Hstep0 & ? & Hprefix1).
  pose (before1 := (local1, global1)).
  inversion Hstep0 as [? ? ? ? ? ? ? ? Htrace0 Hsem0]; subst.
  unfold_write_success_15d34_trace Htrace0. inversion Htrace0; subst.
  cbn in Hsem0. destruct Hsem0 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix1
    ltac:(unfold before1; cbn; discriminate) Hnil HdoneNb) as
    (? & local2 & global2 & ? & prefix2 & Hobs1 & Hstep1 & Hnb2 & Hprefix2).
  pose (before2 := (local2, global2)).
  eapply writeSuccessAssumeCovered in Hstep1; [|reflexivity|exact Hmstatus].
  destruct Hstep1 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix2
    ltac:(unfold before2; cbn; discriminate) Hnil HdoneNb) as
    (? & local3 & global3 & ? & prefix3 & Hobs2 & Hstep2 & ? & Hprefix3).
  pose (before3 := (local3, global3)).
  inversion Hstep2 as [? ? ? ? ? ? ? ? Htrace2 Hsem2]; subst.
  unfold before2 in Htrace2. unfold_write_success_15d34_trace Htrace2.
  inversion Htrace2; subst. cbn in Hsem2. destruct Hsem2 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix3
    ltac:(unfold before3; cbn; discriminate) Hnil HdoneNb) as
    (? & local4 & global4 & ? & prefix4 & Hobs3 & Hstep3 & Hnb4 & Hprefix4).
  pose (before4 := (local4, global4)).
  eapply writeSuccessAssumeCovered in Hstep3; [|reflexivity|exact Halign].
  destruct Hstep3 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix4
    ltac:(unfold before4; cbn; discriminate) Hnil HdoneNb) as
    (? & local5 & global5 & ? & prefix5 & Hobs4 & Hstep4 & ? & Hprefix5).
  pose (before5 := (local5, global5)).
  inversion Hstep4 as [? ? ? ? ? ? ? ? Htrace4 Hsem4]; subst.
  unfold before4 in Htrace4. unfold_write_success_15d34_trace Htrace4.
  inversion Htrace4; subst. cbn in Hsem4. destruct Hsem4 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix5
    ltac:(unfold before5; cbn; discriminate) Hnil HdoneNb) as
    (? & local6 & global6 & ? & prefix6 & Hobs5 & Hstep5 & Hnb6 & Hprefix6).
  eapply writeSuccessReadRegCovered in Hstep5.
  2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: exact Hnb6.
  destruct Hstep5 as (-> & -> & -> & -> & HsymbolicPc).
  cbn in HsymbolicPc. inversion HsymbolicPc as [HpcValue].
  assert (HpcBits : @BV 64 n1 Heq1 = Z_to_bv 64 0x15d34).
  { apply bv_eq. cbn. exact HpcValue. }
  repeat match goal with H : context [@BV 64 n1 Heq1] |- _ => rewrite HpcBits in H end.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix6
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local7 & global7 & ? & prefix7 & Hobs6 & Hstep6 & ? & Hprefix7).
  eapply writeSuccessDefineConstCovered in Hstep6; [|reflexivity|reflexivity].
  destruct Hstep6 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix7
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local8 & global8 & ? & prefix8 & Hobs7 & Hstep7 & Hnb8 & Hprefix8).
  eapply writeSuccessReadRegCovered in Hstep7.
  2: reflexivity. 2: exact Hx1. 2: reflexivity. 2: exact Hnb8.
  destruct Hstep7 as (-> & -> & -> & -> & HsymbolicRa).
  cbn in HsymbolicRa. inversion HsymbolicRa as [HRaValue].
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    (@BV 64 n0 Heq0) ra HRaValue) as HRaBits.
  repeat match goal with H : context [@BV 64 n0 Heq0] |- _ => rewrite HRaBits in H end.
  exists done, labels, spawned, prefix8.
  repeat split; try assumption.
  unfold writeSuccess15d34Prefix8Observations,
    writeSuccess15d34PrefixObservations, writeSuccess15d34Locals.
  cbn. rewrite Hobs5. rewrite Hobs6. rewrite Hobs7.
  rewrite HpcBits. rewrite HRaBits. reflexivity.
Qed.

Print Assumptions segment_15d34_prefix8_covered.
