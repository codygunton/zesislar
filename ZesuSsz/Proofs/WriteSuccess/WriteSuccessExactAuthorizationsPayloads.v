Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Contracts.IslarisMemory.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessEncodeArrays WriteSuccessEncodeWords WriteSuccessOutputSemantic
  WriteSuccessExactEncoderU256Spec WriteSuccessExactTransactionsGasLoads WriteSuccessObservation.

Lemma authorization_u256_payload bytes index :
  (index + 32 <= length bytes)%nat ->
  writeSuccessU256WordsPayload (transactionRowWord bytes index 0)
    (transactionRowWord bytes index 8) (transactionRowWord bytes index 16)
    (transactionRowWord bytes index 24) =
  writeSuccessPrivateBytes (writeSuccessEncodeU256
    (little_endian_to_bv 8 (take 32 (drop index bytes)))).
Proof.
  intros Hbound.
  rewrite /writeSuccessEncodeU256 writeSuccessPrivateEncodeArray.
  2: rewrite length_take length_drop; lia.
  unfold writeSuccessU256WordsPayload.
  rewrite /writeSuccessPrivateBytes !map_app -/writeSuccessPrivateBytes.
  change (writeSuccessPrivateBytes (writeSuccessEncodeU64
    (bv_unsigned (transactionRowWord bytes index 0))) ++
    writeSuccessPrivateBytes (writeSuccessEncodeU64
      (bv_unsigned (transactionRowWord bytes index 8))) ++
    writeSuccessPrivateBytes (writeSuccessEncodeU64
      (bv_unsigned (transactionRowWord bytes index 16))) ++
    writeSuccessPrivateBytes (writeSuccessEncodeU64
      (bv_unsigned (transactionRowWord bytes index 24))) = take 32 (drop index bytes)).
  rewrite !writeSuccessPrivateEncodeU64 /transactionRowWord.
  rewrite !u64_bytes_roundtrip; try (rewrite length_take length_drop; lia).
  rewrite -!drop_drop /= !app_assoc !take_take_drop.
  reflexivity.
Qed.
Print Assumptions authorization_u256_payload.

Lemma authorization_int_payload bytes offset :
  (offset + 8 <= length bytes)%nat ->
  writeSuccessPrivateBytes (writeSuccessEncodeU64
    (bv_unsigned (transactionRowWord bytes 0 offset))) =
  writeSuccessPrivateBytes (writeSuccessEncodeU64
    (little_endian_to_bv 8 (take 8 (drop offset bytes)))).
Proof.
  intros Hbound.
  rewrite /writeSuccessEncodeU64 (writeSuccessPrivateEncodeArray 8 (take 8 (drop offset bytes))).
  2: rewrite length_take length_drop; lia.
  rewrite writeSuccessPrivateEncodeLe /transactionRowWord.
  rewrite Nat.add_0_l u64_bytes_roundtrip; [reflexivity|].
  rewrite length_take length_drop; lia.
Qed.
Print Assumptions authorization_int_payload.
