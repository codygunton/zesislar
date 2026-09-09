From Coq Require Import Eqdep_dec Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.

Lemma segment_15d2c_middle_upper_covered regs global
    (mstatusBits address : bv 64) prefix done labels spawned after :
  eval_a_exp regs writeSuccess15d2cUpper = Some (Val_Bool true) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess15d2cTrace15 mstatusBits address) regs, global) prefix done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists rest, IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess15d2cTraceUpper mstatusBits address) regs, global) rest done /\
  prefix = [writeSuccess15694Observation
    (writeSuccess15694Local (writeSuccess15d2cTraceUpper mstatusBits address) regs) global] ++ rest.
Proof.
  intros Hupper Hprefix Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local & global' & ? & rest & Hobs & Hstep & ? & Hrest).
  eapply writeSuccessAssumeCovered in Hstep; [|reflexivity|exact Hupper].
  destruct Hstep as (-> & -> & -> & ->). exists rest. split; first exact Hrest.
  cbn. rewrite Hobs. reflexivity.
Qed.
Print Assumptions segment_15d2c_middle_upper_covered.
