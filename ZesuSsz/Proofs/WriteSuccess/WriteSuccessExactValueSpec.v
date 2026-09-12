Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.

Import ListNotations.

Definition writeSuccessValueBlockHash (values : list (bv 64)) : list (bv 8) :=
  take 32 (drop 556 (bytes_of_u64s values)).

Lemma writeSuccessBytesOfU64s_length (values : list (bv 64)) :
  Z.of_nat (length (bytes_of_u64s values)) =
  8 * Z.of_nat (length values).
Proof.
  induction values as [|value values IH]; cbn [bytes_of_u64s].
  - reflexivity.
  - rewrite app_length length_bv_to_little_endian; [|lia].
    rewrite Nat2Z.inj_add IH. cbn. lia.
Qed.

Lemma writeSuccessValueBlockHash_length (values : list (bv 64)) :
  length values = 74%nat -> length (writeSuccessValueBlockHash values) = 32%nat.
Proof.
  intros Hvalues.
  have Hbytes : length (bytes_of_u64s values) = 592%nat.
  { apply Nat2Z.inj. rewrite writeSuccessBytesOfU64s_length Hvalues. cbn. lia. }
  rewrite /writeSuccessValueBlockHash length_take length_drop Hbytes.
  cbn. lia.
Qed.

Lemma writeSuccessBytesOfU64s_app left right :
  bytes_of_u64s (left ++ right) =
  bytes_of_u64s left ++ bytes_of_u64s right.
Proof.
  apply flat_map_app.
Qed.

Lemma writeSuccessBytesOfU64s_drop n values :
  bytes_of_u64s (drop n values) = drop (8 * n) (bytes_of_u64s values).
Proof.
  revert values. induction n as [|n IH]; intros [|value values];
    cbn [bytes_of_u64s]; try reflexivity.
  rewrite drop_app length_bv_to_little_endian; [|lia].
  have Hdrop : drop (8 * S n)
      (bv_to_little_endian 8 8 (bv_unsigned value)) = [].
  { apply drop_ge. rewrite length_bv_to_little_endian; lia. }
  rewrite Hdrop. cbn.
  replace (8 * S n - 8)%nat with (8 * n)%nat by lia.
  apply IH.
Qed.

Definition writeSuccessExactValueWord (values : list (bv 64)) (index : nat) :=
  writeSuccessValueWord (take 69 values) index.

Definition writeSuccessExactValueIntEvent
    (sp : bv 64) (values : list (bv 64)) (index : nat)
    (tail : spec) : spec :=
  writeOutputEvents (sp - 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes
      (writeSuccessEncodeU64
        (bv_unsigned (writeSuccessExactValueWord values index)))) tail.

Definition writeSuccessExactValueEventsAfterExtra (sp : bv 64)
    (values : list (bv 64)) (tail : spec) : spec :=
  writeSuccessExactValueIntEvent sp values 6
    (writeOutputEvents (sp + 1588)%bv (BV 64 32)
      (writeSuccessValueBlockHash values)
      (writeSuccessExactValueIntEvent sp values 8 tail)).

Definition writeSuccessExactValueEventsAfterInts (sp : bv 64)
    (values : list (bv 64)) (payload : list (bv 8)) (tail : spec) : spec :=
  writeOutputEvents (sp - 48)%bv (BV 64 8)
    (writeSuccessPrivateBytes
      (writeSuccessEncodeU64
        (bv_unsigned (writeSuccessExactValueWord values 5))))
    (writeOutputEvents (writeSuccessExactValueWord values 4)
      (writeSuccessExactValueWord values 5) payload
      (writeSuccessExactValueEventsAfterExtra sp values tail)).

Definition writeSuccessExactValueEventsAfter2 (sp : bv 64)
    (values : list (bv 64)) (payload : list (bv 8)) (tail : spec) : spec :=
  writeSuccessExactValueIntEvent sp values 3
    (writeSuccessExactValueEventsAfterInts sp values payload tail).

Definition writeSuccessExactValueEventsAfter1 (sp : bv 64)
    (values : list (bv 64)) (payload : list (bv 8)) (tail : spec) : spec :=
  writeSuccessExactValueIntEvent sp values 2
    (writeSuccessExactValueEventsAfter2 sp values payload tail).

Definition writeSuccessExactValueEventsAfter0 (sp : bv 64)
    (values : list (bv 64)) (payload : list (bv 8)) (tail : spec) : spec :=
  writeSuccessExactValueIntEvent sp values 1
    (writeSuccessExactValueEventsAfter1 sp values payload tail).

Definition writeSuccessExactValueEvents (sp : bv 64)
    (values : list (bv 64)) (payload : list (bv 8)) (tail : spec) : spec :=
  writeSuccessExactValueIntEvent sp values 0
    (writeSuccessExactValueEventsAfter0 sp values payload tail).

Definition writeSuccessExactValueMemory `{!islaG Sigma}
    (sp : bv 64) (values : list (bv 64)) : iProp Sigma :=
  ((bv_unsigned sp + 1032) ↦ₘ∗ take 69 values ∗
   (bv_unsigned sp + 1584) ↦ₘ∗ take 4 (drop 552 (bytes_of_u64s values)) ∗
   (bv_unsigned sp + 1588) ↦ₘ∗ writeSuccessValueBlockHash values ∗
   (bv_unsigned sp + 1620) ↦ₘ∗ drop 588 (bytes_of_u64s values))%I.

Global Instance : LithiumUnfold (@writeSuccessExactValueMemory) := I.

Lemma writeSuccessExactValueMemory_from_bytes `{!islaG Sigma}
    (sp : bv 64) (bytes : list (bv 8)) (values : list (bv 64)) :
  length values = 74%nat ->
  bytes_of_u64s values = take 592 bytes ->
  (bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes -∗
  writeSuccessExactValueMemory sp values.
Proof.
  intros Hlength Hbytes. iIntros "Hmemory".
  iEval (rewrite -Hbytes) in "Hmemory".
  iPoseProof (mem_mapsto_bytes_to_u64_array with "Hmemory") as "Hvalues".
  iDestruct (mem_mapsto_array_app 64%N (bv_unsigned sp + 1032)
    (DfracOwn 1) (take 69 values) (drop 69 values) with "[Hvalues]")
    as "[Hprefix Hsuffix]".
  { rewrite take_drop. iFrame. }
  have HprefixLength : length (take 69 values) = 69%nat.
  { rewrite length_take Hlength. lia. }
  iEval (rewrite HprefixLength /=) in "Hsuffix".
  iPoseProof (mem_mapsto_u64_array_to_bytes with "Hsuffix") as "Hsuffix".
  iEval (rewrite writeSuccessBytesOfU64s_drop) in "Hsuffix".
  iEval (replace (bv_unsigned sp + 1032 + 8 * 69%nat) with
    (bv_unsigned sp + 1584) by lia) in "Hsuffix".
  iEval (rewrite -(take_drop 4 (drop 552 (bytes_of_u64s values)))) in "Hsuffix".
  iDestruct (mem_mapsto_array_app 8%N (bv_unsigned sp + 1584)
    (DfracOwn 1) (take 4 (drop 552 (bytes_of_u64s values)))
    (drop 4 (drop 552 (bytes_of_u64s values))) with "Hsuffix")
    as "[Hfour Hrest]".
  iEval (rewrite /= drop_drop Nat.add_comm) in "Hrest".
  have HbytesLength : length (bytes_of_u64s values) = 592%nat.
  { apply Nat2Z.inj. rewrite writeSuccessBytesOfU64s_length Hlength. cbn. lia. }
  have HfourLength : length (take 4 (drop 552 (bytes_of_u64s values))) = 4%nat.
  { rewrite length_take length_drop HbytesLength. lia. }
  iEval (rewrite HfourLength /=) in "Hrest".
  iEval (replace (bv_unsigned sp + 1584 + 4) with
    (bv_unsigned sp + 1588) by lia) in "Hrest".
  iEval (rewrite -(take_drop 32 (drop 556 (bytes_of_u64s values)))) in "Hrest".
  iDestruct (mem_mapsto_array_app 8%N (bv_unsigned sp + 1588)
    (DfracOwn 1) (take 32 (drop 556 (bytes_of_u64s values)))
    (drop 32 (drop 556 (bytes_of_u64s values))) with "Hrest")
    as "[Hhash Htail]".
  iEval (rewrite /= drop_drop Nat.add_comm) in "Htail".
  have HhashLength : length (take 32 (drop 556 (bytes_of_u64s values))) = 32%nat.
  { rewrite length_take length_drop HbytesLength. lia. }
  iEval (rewrite HhashLength /=) in "Htail".
  iEval (replace (bv_unsigned sp + 1588 + 32) with
    (bv_unsigned sp + 1620) by lia) in "Htail".
  rewrite /writeSuccessExactValueMemory /writeSuccessValueBlockHash.
  iFrame.
Qed.

Print Assumptions writeSuccessExactValueMemory_from_bytes.

Definition writeSuccessExactValuePost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessValueRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (default (BV 64 0) (take 69 values !! 8%nat)) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 0) ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   writeSuccessExactValueMemory sp values ∗
   bv_unsigned (writeSuccessExactValueWord values 4) ↦ₘ∗ payload ∗
   (bv_unsigned sp + 104) ↦ₘ default (BV 64 0) (take 69 values !! 7%nat) ∗
   (bv_unsigned sp + 112) ↦ₘ default (BV 64 0) (take 69 values !! 8%nat) ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Definition writeSuccessExactValueSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessHeaderRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 104) ↦ₘ? 16 ∗
    writeSuccessExactValueMemory sp values ∗
    bv_unsigned (writeSuccessExactValueWord values 4) ↦ₘ∗ payload ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessExactValueEvents sp values payload tail) ∗
    ⌜length values = 74%nat⌝ ∗
    ⌜bv_unsigned (writeSuccessExactValueWord values 5) = length payload⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗
    instr_pre 0x14f04 (writeSuccessExactValuePost sp values payload tail P))%I.

Global Instance : LithiumUnfold (@writeSuccessExactValueSpec) := I.
Global Instance : LithiumUnfold (@writeSuccessExactValuePost) := I.

Definition writeSuccessExactValueHandoffRegisters : list string :=
  ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessExactValueHandoffRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessExactValueHandoffRegisters.

Definition writeSuccessExactValueBaseFeeReturnSpec
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (b8 b9 stack2 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x14ed4) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp + 1588)%bv (BV 64 32)
        (writeSuccessValueBlockHash values)
        (writeSuccessExactValueIntEvent sp values 8 tail)) ∗
    ("x6" ↦ᵣ: fun r6 => ⌜valu_has_shape r6 (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits b8 ∗ "x9" ↦ᵣ RVal_Bits b9 ∗
    (bv_unsigned sp - 48) ↦ₘ? Z.of_nat 8%nat ∗
    (bv_unsigned sp - 40) ↦ₘ (BV 64 0x15c90) ∗
    (bv_unsigned sp - 32) ↦ₘ stack2 ∗
    (bv_unsigned sp - 24) ↦ₘ b9 ∗
    reg_col writeSuccessExactValueHandoffRegShapes ∗
    (bv_unsigned sp + 104) ↦ₘ? 16 ∗
    writeSuccessExactValueMemory sp values ∗
    bv_unsigned (writeSuccessExactValueWord values 4) ↦ₘ∗ payload ∗
    P ∗
    instr_pre 0x14f04
      (writeSuccessExactValuePost sp values payload tail P) ∗
    ⌜length values = 74%nat⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessExactValueBaseFeeReturnSpec) := I.
