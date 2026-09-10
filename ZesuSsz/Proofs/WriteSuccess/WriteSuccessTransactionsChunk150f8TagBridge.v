Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.

Import ListNotations.

Lemma write_success_transactions_split_u64_tag
    `{!islaG Sigma} `{!threadG}
    (address : Z) (word : bv 64) (tag : bv 8)
    (tail : list (bv 8)) :
  address ↦ₘ word -∗
  ⌜bv_to_little_endian 8 8 (bv_unsigned word) = tag :: tail⌝ -∗
  address ↦ₘ tag ∗
  (address + 1) ↦ₘ∗ tail.
Proof.
  iIntros "Hword" (Hshape).
  iDestruct (mem_mapsto_mapsto_to_byte_array with "Hword") as "Hbytes".
  iEval (rewrite Hshape) in "Hbytes".
  iDestruct (mem_mapsto_array_app 8%N address (DfracOwn 1)
    [tag] tail with "Hbytes") as "[Htag Htail]".
  iDestruct (mem_mapsto_array_singleton with "Htag") as "Htag".
  have Haddress :
      (address + Z.of_N (8 `div` 8) * length [tag])%Z = address + 1 by
    change (address + 1 * 1 = address + 1)%Z; lia.
  iEval (rewrite Haddress) in "Htail".
  iFrame.
Qed.
