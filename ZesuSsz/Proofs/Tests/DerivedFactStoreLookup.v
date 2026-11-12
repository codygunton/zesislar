Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A store into an uninitialized cell at p + 8, where the range of p comes only
   from a folded domain predicate through a registered derivation. *)
Record SlotArgs := { slotPointer : Z }.
Record SlotDomain (args : SlotArgs) : Prop := {
  slot_domain_range : 0 <= slotPointer args < 2 ^ 64;
  slot_domain_end : slotPointer args + 16 <= 3221225472
}.
#[local] Instance slot_domain_derived (args : SlotArgs) :
  ZesuSsz.Automation.PureFacts.ZesuDerivedFacts (SlotDomain args)
    ((0 <= slotPointer args < 2 ^ 64) /\ slotPointer args + 16 <= 3221225472) :=
  fun H => conj (slot_domain_range _ H) (slot_domain_end _ H).

Lemma derived_range_at_uninit_store `{!islaG Sigma} `{!threadG} (args : SlotArgs) :
  SlotDomain args ->
  (slotPointer args + 8) ↦ₘ? 8 -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (Z_to_bv 64 (slotPointer args) + BV 64 8)))
    (fun _ => True)%I.
Proof. intros Hdomain. iIntros "Hslot". zesu_block2. Qed.
