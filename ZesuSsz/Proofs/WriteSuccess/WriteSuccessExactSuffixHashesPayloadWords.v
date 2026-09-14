Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma suffix_row_word source index offset :
  (offset + 8 <= 32)%nat ->
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop offset (take 32 (drop index source))))) =
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + offset)%nat source))).
Proof.
  intros Hoffset.
  rewrite (take_drop_commute (take 32 (drop index source)) 8 offset) take_take.
  rewrite Nat.min_l; [|lia].
  rewrite -(take_drop_commute (drop index source) 8 offset) drop_drop.
  reflexivity.
Qed.
Print Assumptions suffix_row_word.
