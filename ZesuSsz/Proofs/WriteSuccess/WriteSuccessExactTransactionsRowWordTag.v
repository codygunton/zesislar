Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.ByteArrays.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.

Lemma transactions_row_word_tag bytes index offset :
  (index + offset + 8 <= length bytes)%nat ->
  bv_extract 0 8 (transactionRowWord bytes index offset) =
    default (BV 8 0) (bytes !! (index + offset)%nat).
Proof.
  intros Hlength. unfold transactionRowWord.
  rewrite zesu_take_8_drop; [|lia].
  unfold little_endian_to_bv. cbn.
  apply bv_eq. bv_simplify. bitblast as bit.
  all: (f_equal; lia).
Qed.
Print Assumptions transactions_row_word_tag.
