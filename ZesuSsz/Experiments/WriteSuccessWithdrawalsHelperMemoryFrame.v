From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsMemoryFrameLowScratch sp before after frame :
  writeSuccessWithdrawalsMemoryFrame sp before frame ->
  writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16 after before ->
  writeSuccessWithdrawalsMemoryFrame sp after frame.
Proof.
  intros [HbeforeDom Hbefore] [HafterDom Hafter]. split.
  - rewrite HafterDom. exact HbeforeDom.
  - intros address Hlow Hhigh. rewrite Hafter; last (intro Hin; apply Hlow; lia).
    apply Hbefore; assumption.
Qed.

Lemma writeSuccessWithdrawalsMemoryFrameHighScratch sp before after frame :
  writeSuccessWithdrawalsMemoryFrame sp before frame ->
  writeSuccessMemoryRangeFrame (bv_unsigned sp + 1744) 48 after before ->
  writeSuccessWithdrawalsMemoryFrame sp after frame.
Proof.
  intros [HbeforeDom Hbefore] [HafterDom Hafter]. split.
  - rewrite HafterDom. exact HbeforeDom.
  - intros address Hlow Hhigh. rewrite Hafter; last (intro Hin; apply Hhigh; lia).
    apply Hbefore; assumption.
Qed.

Lemma writeSuccessWithdrawalsMemoryFramesLookup sp before after frame address :
  writeSuccessWithdrawalsMemoryFrame sp before frame ->
  writeSuccessWithdrawalsMemoryFrame sp after frame ->
  ~ (bv_unsigned sp - 16 <= bv_unsigned address < bv_unsigned sp) ->
  ~ (bv_unsigned sp + 1744 <= bv_unsigned address < bv_unsigned sp + 1792) ->
  after !! address = before !! address.
Proof.
  intros [_ Hbefore] [_ Hafter] Hlow Hhigh.
  rewrite (Hafter address Hlow Hhigh).
  rewrite (Hbefore address Hlow Hhigh).
  reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsMemoryFrameLowScratch.
Print Assumptions writeSuccessWithdrawalsMemoryFrameHighScratch.
Print Assumptions writeSuccessWithdrawalsMemoryFramesLookup.
