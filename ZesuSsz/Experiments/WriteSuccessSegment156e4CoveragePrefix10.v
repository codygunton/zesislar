(* Generated from the pinned bnez trace shape. *)
(* The renderer validates the pinned operands and endpoints. *)
From Coq Require Import Eqdep_dec.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156e4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.

Definition writeSuccess156e4Second4Observations value condition regs global :=
  skipn 6 (writeSuccess156e4CommonObservations value condition regs global).

Lemma segment_156e4_prefix10_covered regs global (value : bv 64)
    (condition : bool) prefix6 done :
  regs !! "x9" = Some (RVal_Bits value) ->
  eval_exp (writeSuccess156e4Condition value) = Some (Val_Bool condition) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess156e4Trace6 condition) regs, global)
    prefix6 done ->
  done.1.(seq_trace) = tnil ->
  done.1.(seq_nb_state) = false ->
  exists prefix10,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess156e4Trace10 value condition) regs, global)
      prefix10 done /\
    prefix6 = writeSuccess156e4Second4Observations
      value condition regs global ++ prefix10.
Proof.
  intros Hx9 Hcondition Hprefix6 Hnil HdoneNb.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix6
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local7 & global7 & ? & prefix7 & Hobs6 & Hstep6 & ? & Hprefix7).
  pose (before7 := (local7, global7)).
  inversion Hstep6 as [? ? ? ? ? ? ? ? Htrace6 Hsem6]; subst.
  cbn [writeSuccess156e4Trace6 writeSuccess156e4Trace5
    writeSuccess156e4Trace4 writeSuccess156e4Trace3
    writeSuccess156e4Trace2 writeSuccess156e4Trace1
    writeSuccess156e4NextPc writeSuccessTraceTail a156e4] in Htrace6.
  inversion Htrace6; subst. cbn in Hsem6. destruct Hsem6 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix7
    ltac:(unfold before7; cbn; discriminate) Hnil HdoneNb) as
    (? & local8 & global8 & ? & prefix8 & Hobs7 & Hstep7 & Hnb8 & Hprefix8).
  eapply writeSuccessReadRegCovered in Hstep7.
  2: reflexivity. 2: exact Hx9. 2: reflexivity. 2: exact Hnb8.
  destruct Hstep7 as (-> & -> & -> & -> & HsymbolicLeft).
  cbn in HsymbolicLeft. inversion HsymbolicLeft as [HvalueValue].
  pose proof (inj_pair2_eq_dec N (Coq.NArith.BinNat.N.eq_dec)
    (fun width => bv width) 64%N (@BV 64 n Heq) value HvalueValue)
    as HvalueBits.
  repeat match goal with
  | H : context [@BV 64 n Heq] |- _ => rewrite HvalueBits in H
  end.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix8
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local9 & global9 & ? & prefix9 & Hobs8 & Hstep8 & ? & Hprefix9).
  rename Hobs8 into HobsCondition.
  eapply writeSuccessDefineConstCovered in Hstep8; [|reflexivity|exact Hcondition].
  destruct Hstep8 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix9
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local10 & global10 & ? & prefix10 & Hobs9 & Hstep9 & ? & Hprefix10).
  rename Hobs9 into HobsTarget.
  eapply writeSuccessDefineConstCovered in Hstep9; [|reflexivity|reflexivity].
  destruct Hstep9 as (-> & -> & -> & ->).
  exists prefix10. split; first exact Hprefix10.
  unfold writeSuccess156e4Second4Observations,
    writeSuccess156e4CommonObservations, writeSuccess156e4CommonLocals.
  cbn. rewrite Hobs7. rewrite HobsCondition. rewrite HobsTarget.
  rewrite HvalueBits. reflexivity.
Qed.

Print Assumptions segment_156e4_prefix10_covered.
