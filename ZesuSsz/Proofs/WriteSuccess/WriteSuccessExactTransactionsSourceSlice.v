Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.

Lemma transactions_source_slice (bytes : list (bv 8)) (index offset width : nat) :
  (index + offset + width <= length bytes)%nat ->
  ((fun i => default (BV 8 0) (bytes !! (index + (offset + i))%nat)) <$> seq 0 width) =
    take width (drop (index + offset)%nat bytes).
Proof.
  intros Hbound. apply list_eq. intros i. rewrite list_lookup_fmap.
  destruct (decide (i < width)%nat) as [Hi | Hi].
  - rewrite lookup_seq_lt; [|done]. cbn.
    rewrite lookup_take; [|done]. rewrite lookup_drop.
    replace (index + offset + i)%nat with (index + (offset + i))%nat by lia.
    destruct (lookup_lt_is_Some_2 bytes (index + (offset + i))%nat) as [byte Hbyte]; [lia|].
    rewrite Hbyte. reflexivity.
  - rewrite lookup_seq_ge; [|lia]. rewrite lookup_take_ge; [done | lia].
Qed.
Print Assumptions transactions_source_slice.
