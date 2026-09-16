Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.

Lemma storage_keys_four_words_bytes `{!islaG Sigma}
    (base : Z) (a b c d : bv 64) :
  base ↦ₘ a -∗ (base + 8) ↦ₘ b -∗
  (base + 16) ↦ₘ c -∗ (base + 24) ↦ₘ d -∗
  base ↦ₘ∗ bytes_of_u64s [a;b;c;d].
Proof.
  iIntros "Ha Hb Hc Hd".
  iEval (rewrite -(mem_mapsto_array_singleton 64 base (DfracOwn 1) a)) in "Ha".
  iEval (rewrite -(mem_mapsto_array_singleton 64 (base + 8) (DfracOwn 1) b)) in "Hb".
  iEval (rewrite -(mem_mapsto_array_singleton 64 (base + 16) (DfracOwn 1) c)) in "Hc".
  iEval (rewrite -(mem_mapsto_array_singleton 64 (base + 24) (DfracOwn 1) d)) in "Hd".
  iAssert ((base + 16) ↦ₘ∗ [c;d])%I with "[Hc Hd]" as "Hcd".
  { iApply (mem_mapsto_array_app_combine 64 (base + 16) (DfracOwn 1) [c] [d]
      with "Hc"). cbn. replace (base + 16 + 8)%Z with (base + 24)%Z by lia.
    iExact "Hd". }
  iAssert ((base + 8) ↦ₘ∗ [b;c;d])%I with "[Hb Hcd]" as "Hbcd".
  { iApply (mem_mapsto_array_app_combine 64 (base + 8) (DfracOwn 1) [b] [c;d]
      with "Hb"). cbn. replace (base + 8 + 8)%Z with (base + 16)%Z by lia.
    iExact "Hcd". }
  iApply mem_mapsto_u64_array_to_bytes.
  iApply (mem_mapsto_array_app_combine 64 base (DfracOwn 1) [a] [b;c;d]
    with "Ha"). cbn. iExact "Hbcd".
Qed.
Print Assumptions storage_keys_four_words_bytes.

Lemma storage_keys_u64_chunks (key : list (bv 8)) :
  u64s_of_bytes 4 key =
  [Z_to_bv 64 (little_endian_to_bv 8 (take 8 key));
   Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 key)));
   Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 16 key)));
   Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 key)))].
Proof. unfold u64s_of_bytes. cbn. rewrite !drop_drop. reflexivity. Qed.
Print Assumptions storage_keys_u64_chunks.

Lemma storage_keys_packed_payload (key : list (bv 8)) :
  length key = 32%nat ->
  bytes_of_u64s
    [Z_to_bv 64 (little_endian_to_bv 8 (take 8 key));
     Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 key)));
     Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 16 key)));
     Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 key)))] = key.
Proof.
  intros Hlength. rewrite -storage_keys_u64_chunks.
  apply bytes_of_u64s_of_bytes. exact Hlength.
Qed.
Print Assumptions storage_keys_packed_payload.

Lemma storage_keys_payload_resources `{!islaG Sigma} (base : Z)
    (key : list (bv 8)) :
  length key = 32%nat ->
  base ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 key)) -∗
  (base + 8) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 key))) -∗
  (base + 16) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 16 key))) -∗
  (base + 24) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 key))) -∗
  base ↦ₘ∗ key.
Proof.
  intros Hlength. iIntros "Ha Hb Hc Hd".
  iPoseProof (storage_keys_four_words_bytes with "Ha Hb Hc Hd") as "Hpayload".
  iEval (rewrite (storage_keys_packed_payload key Hlength)) in "Hpayload".
  iExact "Hpayload".
Qed.
Print Assumptions storage_keys_payload_resources.

Lemma storage_keys_bytes_four_words `{!islaG Sigma}
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
Print Assumptions storage_keys_bytes_four_words.
