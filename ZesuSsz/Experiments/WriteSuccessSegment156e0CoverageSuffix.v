From Coq Require Import Eqdep_dec.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156e0.
Require Import IslaTraces.write_success_95.a156e4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0.

Definition writeSuccess156e0TailObservations regs global sp :=
  skipn 5 (writeSuccess156e0PrefixObservations regs global sp) ++
  [writeSuccess156e0Observation (writeSuccess156e0After regs global sp).1 global].

Lemma segment_156e0_suffix_covered regs global (sp : bv 64) oldX9
    prefix5 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e0)) ->
  regs !! "x9" = Some (RVal_Bits sp) ->
  regs !! "x9" = Some oldX9 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e4 = Some a156e4 ->
  IslaInstructionPrefixPath
    (writeSuccess156e0Local writeSuccess156e0Trace5 regs, global)
    prefix5 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess156e0After regs global sp /\
  prefix5 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess156e0TailObservations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix5
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l6 & g6 & ? & p6 & Ho5 & Hs5 & ? & Hp6).
  pose (b6 := (l6,g6)). inversion Hs5 as [? ? ? ? ? ? ? ? Ht5 Hsem5]; subst.
  unfold b6 in Ht5. cbn [writeSuccess156e0Trace5 writeSuccess156e0Trace4
    writeSuccess156e0Trace3 writeSuccess156e0Trace2 writeSuccess156e0Trace1
    writeSuccess156e0NextPc writeSuccessTraceTail a156e0] in Ht5.
  inversion Ht5; subst. cbn in Hsem5. destruct Hsem5 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp6
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l7 & g7 & ? & p7 & Ho6 & Hs6 & Hnb7 & Hp7).
  eapply writeSuccessReadRegCovered in Hs6.
  2: reflexivity. 2: exact Hsp. 2: reflexivity. 2: exact Hnb7.
  destruct Hs6 as (-> & -> & -> & -> & HsymSp).
  cbn in HsymSp. inversion HsymSp as [HspValue].
  match goal with
  | [ Hvalue : existT _ (@BV 64 ?n ?Hwf) = existT _ sp |- _ ] =>
      pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
        (@BV 64 n Hwf) sp Hvalue) as HspBits
  end.
  repeat match goal with H : context [@BV 64 ?n ?Hwf] |- _ =>
    rewrite HspBits in H end.
  destruct (writeSuccess15694TakeStep _ _ _ Hp7
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l8 & g8 & ? & p8 & Ho7 & Hs7 & ? & Hp8).
  eapply writeSuccessDefineConstCovered in Hs7; [|reflexivity|reflexivity].
  destruct Hs7 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp8
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l9 & g9 & ? & p9 & Ho8 & Hs8 & ? & Hp9).
  eapply writeSuccessWriteRegCovered in Hs8.
  2: reflexivity. 2: exact Hdest. 2: reflexivity. 2: reflexivity.
  destruct Hs8 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp9
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l10 & g10 & ? & p10 & Ho9 & Hs9 & ? & Hp10).
  eapply writeSuccessWriteRegCovered in Hs9.
  2: reflexivity. 2: rewrite lookup_insert_ne; last done; exact Hpc.
  2: reflexivity. 2: reflexivity.
  destruct Hs9 as (-> & -> & -> & ->).
  inversion Hp10; subst; last contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity.
  2: { unfold writeSuccess156e0Regs. rewrite lookup_insert. reflexivity. }
  2: { rewrite writeSuccess156e0NextPcExact. exact Hnext. }
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned. destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
  split; first reflexivity.
  unfold writeSuccess156e0TailObservations,
    writeSuccess156e0PrefixObservations. cbn. reflexivity.
Qed.

Print Assumptions segment_156e0_suffix_covered.
