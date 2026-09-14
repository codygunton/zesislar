Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.

Lemma zesu_bytes_four_words `{!islaG Sigma}
    (base : Z) (a b c d : bv 64) :
  base ↦ₘ∗ bytes_of_u64s [a;b;c;d] -∗
  base ↦ₘ a ∗ (base + 8) ↦ₘ b ∗
  (base + 16) ↦ₘ c ∗ (base + 24) ↦ₘ d.
Proof.
  iIntros "Hpayload".
  iDestruct (mem_mapsto_bytes_to_u64_array base (DfracOwn 1) [a;b;c;d]
    with "Hpayload") as "Hwords".
  iDestruct (mem_mapsto_array_app 64 base (DfracOwn 1) [a] [b;c;d]
    with "Hwords") as "[Ha Hbcd]".
  iEval (cbn) in "Hbcd".
  iDestruct (mem_mapsto_array_app 64 (base + 8) (DfracOwn 1) [b] [c;d]
    with "Hbcd") as "[Hb Hcd]".
  iEval (cbn) in "Hcd".
  iEval (replace (base + 8 + 8)%Z with (base + 16)%Z by lia) in "Hcd".
  iDestruct (mem_mapsto_array_app 64 (base + 16) (DfracOwn 1) [c] [d]
    with "Hcd") as "[Hc Hd]".
  iEval (cbn) in "Hd".
  iEval (replace (base + 16 + 8)%Z with (base + 24)%Z by lia) in "Hd".
  iEval (rewrite !mem_mapsto_array_singleton) in "Ha Hb Hc Hd".
  iFrame.
Qed.
Print Assumptions zesu_bytes_four_words.

Lemma zesu_bytes32_four_words `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  length bytes = 32%nat ->
  base ↦ₘ∗ bytes -∗
  ∃ a b c d : bv 64,
    base ↦ₘ a ∗ (base + 8) ↦ₘ b ∗
    (base + 16) ↦ₘ c ∗ (base + 24) ↦ₘ d.
Proof.
  intros Hlength. iIntros "Hbytes".
  have Hpacked : bytes_of_u64s (u64s_of_bytes 4 bytes) = bytes.
  { apply bytes_of_u64s_of_bytes. exact Hlength. }
  have Hchunks : u64s_of_bytes 4 bytes =
    [Z_to_bv 64 (little_endian_to_bv 8 (take 8 bytes));
     Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 bytes)));
     Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 16 bytes)));
     Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 bytes)))].
  { unfold u64s_of_bytes. cbn. rewrite !drop_drop. reflexivity. }
  rewrite Hchunks in Hpacked.
  iPoseProof (zesu_bytes_four_words base
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 bytes)))
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 bytes))))
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 16 bytes))))
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 bytes))))
    with "[Hbytes]") as "Hwords".
  { rewrite Hpacked. iExact "Hbytes". }
  iExists _, _, _, _. iExact "Hwords".
Qed.
Print Assumptions zesu_bytes32_four_words.
