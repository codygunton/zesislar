Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Automation.BitvectorFacts.

Lemma successor_tuple_guard_disabled (left right : bv 64)
    (Hselected : bv_signed (bv_zero_extend 128 left) <
      bv_signed (bv_zero_extend 128 right)) :
  bv_unsigned left < bv_unsigned right.
Proof.
  Fail zesu_primitive_tuple_guard_if_enabled.
  now rewrite !zesu_signed_zero_extend_64_128 in Hselected.
Qed.

Require Import ZesuSsz.Automation.Switches.TupleWitness.

Lemma successor_from_69d8 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte) (x13 x15 x16 : bv 64)
    (Hselected : bv_signed (bv_zero_extend 128 (Z_to_bv 64 183)) < bv_signed (bv_zero_extend 128 x13)) :
  "x13" ↦ᵣ RVal_Bits x13 -∗
  "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 183) -∗
  "x15" ↦ᵣ RVal_Bits x15 -∗ "x16" ↦ᵣ RVal_Bits x16 -∗
  decodeItemBranchBase args frameBytes (Z_to_bv 64 (decodeItemInputPointer args)) -∗
  ∃ data : li_prod (bv 64) (li_prod (list byte) unit),
    decodeItemEntryAt800d6a00 args data.2ₗ data.1ₗ.
Proof. zesu_block. Qed.

Lemma successor_from_6a00 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte) (x13 x15 x16 : bv 64)
    (Hselected : bv_signed (bv_zero_extend 128 x13) >= bv_signed (bv_zero_extend 128 (Z_to_bv 64 192))) :
  "x13" ↦ᵣ RVal_Bits x13 -∗
  "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 192) -∗
  "x15" ↦ᵣ RVal_Bits x15 -∗ "x16" ↦ᵣ RVal_Bits x16 -∗
  decodeItemBranchBase args frameBytes (Z_to_bv 64 (decodeItemInputPointer args)) -∗
  ∃ data : li_prod (bv 64) (li_prod (list byte) unit),
    decodeItemEntryAt800d6a64 args data.2ₗ data.1ₗ.
Proof. zesu_block. Qed.

Lemma successor_from_6a64 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte) (x13 x15 x16 : bv 64)
    (Hselected : bv_signed (bv_zero_extend 128 x13) >= bv_signed (bv_zero_extend 128 (Z_to_bv 64 248))) :
  "x13" ↦ᵣ RVal_Bits x13 -∗
  "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 248) -∗
  "x15" ↦ᵣ RVal_Bits x15 -∗ "x16" ↦ᵣ RVal_Bits x16 -∗
  decodeItemBranchBase args frameBytes (Z_to_bv 64 (decodeItemInputPointer args)) -∗
  ∃ data : li_prod (bv 64) (li_prod (list byte) unit),
    decodeItemEntryAt800d6aa8 args data.2ₗ data.1ₗ.
Proof. zesu_block. Qed.

Lemma successor_tuple_guard_structural_goal : True.
Proof. Fail zesu_primitive_tuple_guard_if_enabled. exact I. Qed.

Print Assumptions successor_from_69d8.
Print Assumptions successor_from_6a00.
Print Assumptions successor_from_6a64.
