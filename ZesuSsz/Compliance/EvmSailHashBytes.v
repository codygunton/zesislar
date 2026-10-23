Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SailEval ZesuSsz.Automation.SailBytes.
From Coq Require Import Bool List ZArith Lia.
Require Import SailStdpp.MachineWord SailStdpp.Values SailStdpp.Operators_mwords.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Import ListNotations.
Open Scope Z_scope.

Lemma sail_hash_bytes value :
  projT1 (word_to_hash (Build_word value)) =
    bv_to_little_endian 32 8 value.
Proof.
  unfold word_to_hash. cbn [word_value].
  repeat rewrite sail_get_slice_int by lia.
  change (List.map (fun index : nat => Z_to_bv 8
    (Z.shiftr value (8 * Z.of_nat index))) (List.seq O 32%nat) =
    bv_to_little_endian 32 8 value).
  apply stdpp.list.list_eq. intro index.
  apply (proj2 (stdpp.option.option_eq _ _)). intro item.
  rewrite stdpp.list.list_lookup_fmap_Some.
  rewrite bv_to_little_endian_lookup_Some by lia.
  split.
  - intros [found [Hlookup Hitem]].
    apply stdpp.list_numbers.lookup_seq in Hlookup.
    destruct Hlookup as [Hfound Hindex]. subst found.
    split; [lia |]. rewrite Hitem. f_equal. f_equal. lia.
  - intros [Hindex Hitem]. exists index. split.
    + apply stdpp.list_numbers.lookup_seq. split; [reflexivity | lia].
    + rewrite Hitem. f_equal. f_equal. lia.
Qed.
Print Assumptions sail_hash_bytes.
Lemma sail_hash_fold_reconstruction (input : list byte)
    (Hlength : length input = 32%nat) :
  projT1 (word_to_hash (Build_word
    (fold_left (fun accumulator (item : byte) =>
      Z.add (Z.mul accumulator 256) (@uint 8 item)) input 0))) =
  List.rev input.
Proof.
  rewrite sail_hash_bytes, sail_fold_uint_little_endian.
  apply bv_to_little_endian_to_bv.
  rewrite rev_length, Hlength. reflexivity.
Qed.
Print Assumptions sail_hash_fold_reconstruction.
