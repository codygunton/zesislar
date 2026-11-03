Require Import ZesuSsz.Automation.SourceRegisterOrigin194.
Require Import ZesuSsz.Automation.SourceWitnessInputs.
Require Import isla.riscv64.riscv64.
From stdpp Require Import decidable bitvector.definitions.

Lemma zesu_bvn_same_width203 (width : N) (word : bv width) :
  bvn_to_bv width (bv_to_bvn word) = Some word.
Proof.
  unfold bvn_to_bv. cbn.
  rewrite (decide_True_pi (eq_refl width)).
  reflexivity.
Qed.

Lemma zesu_source_register_post_bits203 `{!islaG Sigma} `{!threadG}
    key width continuation (word : bv width) :
  zesu_source_register_post key width continuation (Val_Bits word) =
  (⌜ZesuSourceWitness key word⌝ -∗ continuation (Val_Bits word))%I.
Proof.
  unfold zesu_source_register_post.
  rewrite zesu_bvn_same_width203. reflexivity.
Qed.
Print Assumptions zesu_bvn_same_width203.
Print Assumptions zesu_source_register_post_bits203.
