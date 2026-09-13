Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma byte_array_forget `{!islaG Sigma} (base : Z) (bytes : list (bv 8)) :
  base ↦ₘ∗ bytes -∗ base ↦ₘ? Z.of_nat (length bytes).
Proof.
  iIntros "Hbytes".
  iDestruct (snapshot_byte_array_to_mapsto with "Hbytes") as "Hword".
  iPoseProof (mem_mapsto_mapsto_to_uninit with "Hword") as "Hmemory".
  iEval (rewrite N.mul_comm N.div_mul //) in "Hmemory".
  rewrite nat_N_Z. iExact "Hmemory".
Qed.
Print Assumptions byte_array_forget.
