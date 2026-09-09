(* Generated from the pinned return trace shape. *)
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.

Lemma segment_101a0_suffix_write_covered regs global (ra : bv 64)
    prefix10 done :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101a0)) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess101a0Trace10 ra) regs, global)
    prefix10 done ->
  done.1.(seq_trace) = tnil -> done.1.(seq_nb_state) = false ->
  exists prefix11,
    IslaInstructionPrefixPath
      (writeSuccess15694Local (writeSuccess101a0Trace11 ra)
        (writeSuccess101a0Regs regs ra), global) prefix11 done /\
    prefix10 = [writeSuccess15694Observation
      (writeSuccess15694Local (writeSuccess101a0Trace11 ra)
        (writeSuccess101a0Regs regs ra)) global] ++ prefix11.
Proof.
  intros Hpc Hprefix Hnil Hnb.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil Hnb) as
    (? & local & nextGlobal & ? & rest & Hobs & Hstep & ? & Hrest).
  eapply writeSuccessWriteRegCovered in Hstep.
  2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: reflexivity.
  destruct Hstep as (-> & -> & -> & ->).
  exists rest. split; first exact Hrest. cbn. rewrite Hobs. reflexivity.
Qed.
Print Assumptions segment_101a0_suffix_write_covered.
