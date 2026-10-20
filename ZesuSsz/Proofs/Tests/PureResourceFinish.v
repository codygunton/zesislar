Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import isla.riscv64.riscv64.

Lemma pure_resource_final_bitvector `{!islaG Sigma} (value : bv 64) :
  ⊢ (⌜(bv_unsigned value < bv_modulus 64)%Z⌝ : iProp Sigma).
Proof.
  iStartProof.
  Fail solve [ZesuSsz.Automation.Finish.zesu_finish_pure_resources_step].
  zesu_run.
Qed.

Print Assumptions pure_resource_final_bitvector.

Lemma pure_resource_finish_bitvector `{!islaG Sigma} (value : bv 64) :
  ⊢ (⌜(bv_unsigned value < bv_modulus 64)%Z⌝ : iProp Sigma).
Proof.
  iStartProof.
  zesu_finish.
Qed.

Print Assumptions pure_resource_finish_bitvector.
