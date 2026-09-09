From Coq Require Import Eqdep_dec Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.

Lemma segment_15d18_middle_pc_covered regs global
    (mstatusBits address : bv 64) prefix done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d18)) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess15d18TraceUpper mstatusBits address) regs, global) prefix done ->
  done.1.(seq_trace) = tnil -> seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists rest, IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess15d18Trace17 mstatusBits address) regs, global) rest done /\
  prefix = map (fun trace => writeSuccess15694Observation (writeSuccess15694Local trace regs) global)
    [writeSuccess15d18Trace16 mstatusBits address; writeSuccess15d18Trace17 mstatusBits address] ++ rest.
Proof.
  intros Hpc Hprefix Hnil Hdone. have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l16 & g16 & ? & p16 & Ho15 & Hs15 & ? & Hp16).
  pose (b16 := (l16,g16)). eapply writeSuccessDeclareConstBitVecCovered in Hs15; [|reflexivity].
  destruct Hs15 as (pcBits & -> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp16 ltac:(unfold b16; cbn; discriminate) Hnil HdoneNb) as
    (? & l17 & g17 & ? & p17 & Ho16 & Hs16 & Hnb17 & Hp17).
  eapply writeSuccessReadRegCovered in Hs16.
  2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: exact Hnb17.
  destruct Hs16 as (-> & -> & -> & -> & HsymPc). cbn in HsymPc. injection HsymPc as HpcValue.
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    pcBits (Z_to_bv 64 0x15d18) HpcValue) as HpcBits. subst pcBits.
  exists p17. split; first exact Hp17. cbn. rewrite Ho15 Ho16. reflexivity.
Qed.
Print Assumptions segment_15d18_middle_pc_covered.
