From Coq Require Import Eqdep_dec Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.

Definition writeSuccess10198MiddleSecondPcObservations regs global
    mstatusBits base :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess10198Trace17 mstatusBits base;
     writeSuccess10198Trace18 mstatusBits base;
     writeSuccess10198Trace19 mstatusBits base].

Lemma segment_10198_middle_second_pc_covered regs global
    (mstatusBits base : bv 64) prefix16 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10198)) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess10198Trace16 mstatusBits base) regs, global)
    prefix16 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists prefix19,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess10198Trace19 mstatusBits base) regs, global)
      prefix19 done /\
    prefix16 = writeSuccess10198MiddleSecondPcObservations regs global
      mstatusBits base ++ prefix19.
Proof.
  intros Hpc Hprefix Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l17 & g17 & ? & p17 & Ho16 & Hs16 & ? & Hp17).
  pose (b17 := (l17,g17)).
  eapply writeSuccessDeclareConstBitVecCovered in Hs16; [|reflexivity].
  destruct Hs16 as (pcBits & -> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp17
    ltac:(unfold b17; cbn; discriminate) Hnil HdoneNb) as
    (? & l18 & g18 & ? & p18 & Ho17 & Hs17 & Hnb18 & Hp18).
  pose (b18 := (l18,g18)). eapply writeSuccessReadRegCovered in Hs17.
  2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: exact Hnb18.
  destruct Hs17 as (-> & -> & -> & -> & HsymPc).
  cbn in HsymPc. injection HsymPc as HpcValue.
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    pcBits (Z_to_bv 64 0x10198) HpcValue) as HpcBits. subst pcBits.
  destruct (writeSuccess15694TakeStep _ _ _ Hp18
    ltac:(unfold b18; cbn; discriminate) Hnil HdoneNb) as
    (? & l19 & g19 & ? & p19 & Ho18 & Hs18 & ? & Hp19).
  eapply writeSuccessDefineConstCovered in Hs18;
    [|reflexivity|reflexivity]. destruct Hs18 as (-> & -> & -> & ->).
  exists p19. split; first exact Hp19.
  unfold writeSuccess10198MiddleSecondPcObservations. cbn.
  rewrite Ho16. rewrite Ho17. rewrite Ho18. reflexivity.
Qed.

Print Assumptions segment_10198_middle_second_pc_covered.
