(* Normal forms of words the txAccessList blocks reload or compute, as
   rewrite hints of the region (exported by TxAccessListLoopIntro.v).
   - A list header word stored as its little-endian bytes and reloaded is the
     eight-byte concatenation of `Z_to_bv 8 (v ≫ 8 i)`: it is `Z_to_bv 64 v`,
     and `v` itself when `v` is a header word of a well-formed list (the memcpy
     source of the growth path +0x3fc, the remap and alloc sizes).
   - The stack bytes of the array-list callees, `96 + 16` in their call specs,
     are 112 (the callee frame handed back after the keysToOwnedSlice call at
     +0x258 meets the caller's frame region in that form). *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Contracts.ArrayListContract.
Local Open Scope Z_scope.

Lemma tx_word_of_shifted_bytes (v : Z) :
  bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
    (bv_concat 16 (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat 7))) (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat 6))))
    (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat 5)))) (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat 4))))
    (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat 3)))) (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat 2))))
    (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat 1)))) (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat 0))) =
  Z_to_bv 64 v.
Proof. bv_simplify. bitblast; f_equal; lia. Qed.

(* The header words of a well-formed list are 64-bit values. *)
Lemma tx_array_list_word_ranges (elementBytes : Z) (state : ArrayListState) :
  0 < elementBytes -> arrayListWellFormed elementBytes state ->
  0 <= arrayListPointer state < 2 ^ 64 /\
  0 <= arrayListLength state < 2 ^ 64 /\
  0 <= arrayListCapacity state < 2 ^ 64.
Proof.
  intros He (Hl & _ & Hp & Hram).
  destruct (Z.eq_dec (arrayListCapacity state) 0) as [Hc|Hc]; [lia|].
  destruct (Hram ltac:(lia)) as [_ Hhi].
  unfold machineRamEnd in Hhi. cbn in Hhi. nia.
Qed.

Ltac tx_word_bound :=
  lazymatch goal with
  | |- 0 <= ?f ?s < 2 ^ 64 =>
      match goal with
      | H : arrayListWellFormed ?e s |- _ =>
          let R := fresh in
          pose proof (tx_array_list_word_ranges e s ltac:(lia) H) as R;
          clear -R; lia
      end
  end.

Lemma tx_unsigned_header_word (v : Z) : 0 <= v < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 v) = v.
Proof. intros Hv. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

#[export] Hint Rewrite tx_word_of_shifted_bytes : zesu_indices isla_coq_rewrite lithium_rewrite.
#[export] Hint Rewrite tx_unsigned_header_word using tx_word_bound
  : zesu_indices isla_coq_rewrite lithium_rewrite.

Lemma tx_array_list_stack_bytes : 96 + 16 = 112.
Proof. reflexivity. Qed.
#[export] Hint Rewrite tx_array_list_stack_bytes : zesu_indices isla_coq_rewrite lithium_rewrite.
