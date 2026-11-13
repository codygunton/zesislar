Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* nextUint64 62d8 at its second store (8 bytes at p + 8, p = result pointer).
   The first store at bv_unsigned (Z_to_bv 64 p) split the 16-byte result
   region, so the free region starts at bv_unsigned (Z_to_bv 64 p) + 8. The
   range of p sits behind the folded domain predicate (a registered
   derivation); the RAM-base branch fact bounds the wrapped address. *)
Record WrapSlotArgs := { wrapSlotPointer : Z }.
Record WrapSlotDomain (args : WrapSlotArgs) : Prop := {
  wrap_slot_base : 2147483648 <= wrapSlotPointer args;
  wrap_slot_range : 0 <= wrapSlotPointer args < 2 ^ 64
}.
#[local] Instance wrap_slot_derived (args : WrapSlotArgs) :
  ZesuSsz.Automation.PureFacts.ZesuDerivedFacts (WrapSlotDomain args)
    (0 <= wrapSlotPointer args < bv_modulus 64) :=
  fun H => wrap_slot_range _ H.

Lemma wrap_lookup_split_region `{!islaG Sigma} (args : WrapSlotArgs) (old : bv 64) :
  WrapSlotDomain args ->
  2684354560 <= bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8) ->
  bv_unsigned (Z_to_bv 64 (wrapSlotPointer args)) ↦ₘ old -∗
  wrapSlotPointer args ↦ₘ?
    (bv_unsigned (Z_to_bv 64 (wrapSlotPointer args)) - wrapSlotPointer args) -∗
  (bv_unsigned (Z_to_bv 64 (wrapSlotPointer args)) + 8) ↦ₘ?
    (wrapSlotPointer args + 16 - (bv_unsigned (Z_to_bv 64 (wrapSlotPointer args)) + 8)) -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8)))
    (λ mk : mem_mapsto_kind,
      match mk with
      | MKMapsTo n' _ => ⌜n' = 64%N⌝ ∗
          (bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8) ↦ₘ BV 64 3 -∗ True)
      | MKArray n' a' l =>
          ⌜(bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8) - a') `mod` 8 = 0⌝ ∗
          ∃ i : nat,
            ⌜Z.of_nat i = (bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8) - a') `div` 8⌝ ∗
            ⌜(i < length l)%nat⌝ ∗
            ∃ Heq : 64%N = n', (a' ↦ₘ∗ <[i := eq_rect 64%N bv (BV 64 3) n' Heq]> l -∗ True)
      | MKUninit a' len =>
          ⌜a' ≤ bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8)⌝ ∗
          ⌜bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8) + 8 ≤ a' + len⌝ ∗
          (bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8) ↦ₘ BV 64 3 -∗
           a' ↦ₘ? (bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8) - a') -∗
           (bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8) + 8) ↦ₘ?
             (a' + len - (bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8) + 8)) -∗
           True)
      | MKMMIO a' len =>
          ⌜a' ≤ bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8)⌝ ∗
          ⌜bv_unsigned (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8) + 8 ≤ a' + len⌝ ∗
          ∃ Pks Pks', spec_trace Pks ∗
            ⌜scons (SWriteMem (Z_to_bv 64 (wrapSlotPointer args) + BV 64 8) (BV 64 3)) Pks' ⊆ Pks⌝ ∗
            (spec_trace Pks' -∗ True)
      end)%I.
Proof. intros Hdomain Hbase. iIntros "Hold Hlow Hhigh". zesu_block2. Qed.
Print Assumptions wrap_lookup_split_region.

(* Refusal: the same address with no range fact for p. The step proves no
   equation and changes nothing; the lookup closes by the exact region. *)
Lemma wrap_lookup_no_range `{!islaG Sigma} (p : Z) :
  bv_unsigned (Z_to_bv 64 p + BV 64 8) ↦ₘ? 8 -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (Z_to_bv 64 p + BV 64 8)))
    (λ mk : mem_mapsto_kind,
      match mk with
      | MKUninit a' len =>
          ⌜a' ≤ bv_unsigned (Z_to_bv 64 p + BV 64 8)⌝ ∗
          ⌜bv_unsigned (Z_to_bv 64 p + BV 64 8) + 8 ≤ a' + len⌝ ∗
          (bv_unsigned (Z_to_bv 64 p + BV 64 8) ↦ₘ BV 64 3 -∗ True)
      | _ => False
      end)%I.
Proof.
  iIntros "Hslot".
  Fail ZesuSsz.Automation2.WrapLookup.zesu_wrap_lookup_retry.
  zesu_block2.
Qed.
Print Assumptions wrap_lookup_no_range.
