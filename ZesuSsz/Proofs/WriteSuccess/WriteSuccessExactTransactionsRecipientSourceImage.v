Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.WordPayloads.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSourceFieldLayout WriteSuccessExactTransactionsSourceSlice.

Lemma transactions_recipient_source_image bytes index :
  (index + 288 <= length bytes)%nat ->
  words_20_payload (transactionRecipientSourceWord bytes index 265)
    (transactionRecipientSourceWord bytes index 273) (transactionRecipientSourceLast bytes index) =
  take 20 (drop (index + 265)%nat bytes).
Proof.
  intros Hbound.
  have Hround8 (chunk : list (bv 8)) (Hlength : length chunk = 8%nat) :
    bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 chunk))) = chunk.
  { have Hrange := little_endian_to_bv_bound 8 chunk. rewrite Hlength in Hrange.
    rewrite Z_to_bv_small; [apply bv_to_little_endian_to_bv; lia | exact Hrange]. }
  have Hround4 (chunk : list (bv 8)) (Hlength : length chunk = 4%nat) :
    bv_to_little_endian 4 8 (bv_unsigned (Z_to_bv 32 (little_endian_to_bv 8 chunk))) = chunk.
  { have Hrange := little_endian_to_bv_bound 8 chunk. rewrite Hlength in Hrange.
    rewrite Z_to_bv_small; [apply bv_to_little_endian_to_bv; lia | exact Hrange]. }
  unfold words_20_payload, transactionRecipientSourceWord, transactionRecipientSourceLast.
  rewrite !transactions_source_slice; [|lia..].
  rewrite Hround4; last (rewrite length_take_le; [reflexivity | rewrite length_drop; lia]).
  rewrite !Hround8; [|rewrite length_take_le; [reflexivity | rewrite length_drop; lia]..].
  replace (index + 273)%nat with (index + 265 + 8)%nat by lia.
  replace (index + 281)%nat with (index + 265 + 8 + 8)%nat by lia.
  rewrite -(drop_drop bytes 8 (index + 265 + 8)).
  rewrite -!(drop_drop bytes 8 (index + 265)).
  rewrite !take_take_drop. reflexivity.
Qed.
Print Assumptions transactions_recipient_source_image.
