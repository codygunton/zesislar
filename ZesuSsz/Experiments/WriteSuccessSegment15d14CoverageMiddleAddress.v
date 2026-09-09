From Coq Require Import Eqdep_dec Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.

Lemma segment_15d14_middle_address_covered regs global
    (mstatusBits declAddress actualAddress : bv 64) prefix done labels spawned after :
  regs !! "x2" = Some (RVal_Bits actualAddress) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess15d14Trace17 mstatusBits declAddress) regs, global) prefix done ->
  done.1.(seq_trace) = tnil -> seq_step done.1 done.2 labels after.1 after.2 spawned ->
  declAddress = actualAddress /\ exists rest, IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess15d14Trace20 mstatusBits actualAddress) regs, global) rest done /\
  prefix = map (fun trace => writeSuccess15694Observation (writeSuccess15694Local trace regs) global)
    [writeSuccess15d14Trace18 mstatusBits actualAddress; writeSuccess15d14Trace19 mstatusBits actualAddress;
     writeSuccess15d14Trace20 mstatusBits actualAddress] ++ rest.
Proof.
  intros Hx2 Hprefix Hnil Hdone. have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l18 & g18 & ? & p18 & Ho17 & Hs17 & ? & Hp18).
  pose (b18 := (l18,g18)). eapply writeSuccessDefineConstCovered in Hs17; [|reflexivity|reflexivity].
  destruct Hs17 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp18 ltac:(unfold b18; cbn; discriminate) Hnil HdoneNb) as
    (? & l19 & g19 & ? & p19 & Ho18 & Hs18 & Hnb19 & Hp19).
  pose (b19 := (l19,g19)). eapply writeSuccessReadRegCovered in Hs18.
  2: reflexivity. 2: exact Hx2. 2: reflexivity. 2: exact Hnb19.
  destruct Hs18 as (-> & -> & -> & -> & HsymAddress). cbn in HsymAddress. injection HsymAddress as HaddressValue.
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    declAddress actualAddress HaddressValue) as HaddressBits. subst declAddress.
  destruct (writeSuccess15694TakeStep _ _ _ Hp19 ltac:(unfold b19; cbn; discriminate) Hnil HdoneNb) as
    (? & l20 & g20 & ? & p20 & Ho19 & Hs19 & ? & Hp20).
  eapply writeSuccessDefineConstCovered in Hs19. 2: reflexivity.
  2: { cbn. destruct (decide (64%N = 64%N)) as [Heq|Hneq].
       - rewrite (UIP_dec N.eq_dec Heq eq_refl). cbn. reflexivity.
       - exfalso. apply Hneq. reflexivity. }
  destruct Hs19 as (-> & -> & -> & ->). split; first reflexivity. exists p20.
  split; first exact Hp20. cbn. rewrite Ho17 Ho18 Ho19. reflexivity.
Qed.
Print Assumptions segment_15d14_middle_address_covered.
