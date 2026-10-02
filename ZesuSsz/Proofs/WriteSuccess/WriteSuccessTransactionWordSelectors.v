Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Spec.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
Lemma transaction_word_stack_selector (sp : bv 64) (bytes : list (bv 8)) (offset : Z) :
  (1744 <= offset <= 1896)%Z ->
  (mapRamBase defaultMap <= bv_unsigned sp)%Z ->
  (bv_unsigned sp + 1896 < machineRamEnd defaultMap)%Z ->
  Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8)
    (drop (Z.to_nat (bv_unsigned (sp + Z_to_bv 64 offset)%bv -
      (bv_unsigned sp + 1744))) bytes))) =
  transactionRowWord bytes (Z.to_nat (offset - 1744)) 0.
Proof.
  intros Hoffset Hlow Hhigh.
  rewrite (stack_array_index sp 1744 offset 1896); [|lia|exact Hlow|exact Hhigh].
  unfold transactionRowWord. rewrite Nat.add_0_r. reflexivity.
Qed.
Print Assumptions transaction_word_stack_selector.
Lemma transaction_words_stack_payload (sp : bv 64) (bytes : list (bv 8)) (index : Z) :
  (0 <= index <= 112)%Z ->
  (mapRamBase defaultMap <= bv_unsigned sp)%Z ->
  (bv_unsigned sp + 1896 < machineRamEnd defaultMap)%Z ->
  WriteSuccessExactEncoderU256Spec.writeSuccessU256WordsPayload
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat (bv_unsigned (sp + Z_to_bv 64 (1744 + index))%bv - (bv_unsigned sp + 1744))) bytes))))
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat (bv_unsigned (sp + Z_to_bv 64 (1752 + index))%bv - (bv_unsigned sp + 1744))) bytes))))
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat (bv_unsigned (sp + Z_to_bv 64 (1760 + index))%bv - (bv_unsigned sp + 1744))) bytes))))
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat (bv_unsigned (sp + Z_to_bv 64 (1768 + index))%bv - (bv_unsigned sp + 1744))) bytes)))) =
  WriteSuccessExactEncoderU256Spec.writeSuccessU256WordsPayload
    (transactionRowWord bytes (Z.to_nat index) 0)
    (transactionRowWord bytes (Z.to_nat index) 8)
    (transactionRowWord bytes (Z.to_nat index) 16)
    (transactionRowWord bytes (Z.to_nat index) 24).
Proof.
  intros Hindex Hlow Hhigh.
  unfold transactionRowWord.
  repeat (rewrite (stack_array_index sp 1744 _ 1896); [|lia|exact Hlow|exact Hhigh]).
  replace (1744 + index - 1744)%Z with index by lia.
  replace (1752 + index - 1744)%Z with (index + 8)%Z by lia.
  replace (1760 + index - 1744)%Z with (index + 16)%Z by lia.
  replace (1768 + index - 1744)%Z with (index + 24)%Z by lia.
  repeat (rewrite Z2Nat.inj_add; [|lia|lia]).
  rewrite Nat.add_0_r. reflexivity.
Qed.
Print Assumptions transaction_words_stack_payload.

