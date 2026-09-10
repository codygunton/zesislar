From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessLoopCommon.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSpec.

Definition writeSuccessBlobHashesLbuOuterFrame `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗
   "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   writeSuccessBlobHashesScratch sp ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessBlobHashesEvents sp (S remaining) tail) ∗ P ∗
   writeSuccessFixedWidthArrayInvariant
     sp pointer base total processed remaining bytes ∗
   instr_pre 0x15564
     (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesLbuOuterFrame) := I.

Definition writeSuccessBlobHashesLbuEntry `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessBlobHashesBodyOtherRegShapes ∗
    "x19" ↦ᵣ RVal_Bits pointer ∗ base ↦ₘ∗ bytes ∗
    writeSuccessBlobHashesLbuOuterFrame P sp pointer base total processed
      remaining bytes tail ∗
    ⌜length bytes = (32 * (processed + S remaining))%nat⌝ ∗
    ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
    ⌜0x20000000 <= base⌝ ∗
    ⌜base + Z.of_nat (length bytes) < 0x40000000⌝)%I.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesLbuEntry) := I.

Definition writeSuccessBlobHashesLbuState `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (target : string) (index offset : nat)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (delete index writeSuccessBlobHashesBodyOtherRegShapes) ∗
   (target ↦ᵣ: fun _ => True) ∗ "x19" ↦ᵣ RVal_Bits pointer ∗
   (bv_unsigned pointer + Z.of_nat offset) ↦ₘ byte ∗
   base ↦ₘ∗ take (32 * processed) bytes ∗
   bv_unsigned pointer ↦ₘ∗ take offset (drop (32 * processed) bytes) ∗
   (bv_unsigned pointer + Z.of_nat (S offset)) ↦ₘ∗
     drop (S offset) (drop (32 * processed) bytes) ∗
   ⌜drop (32 * processed) bytes !! offset = Some byte⌝ ∗
   ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
   ⌜0x20000000 <= bv_unsigned pointer + Z.of_nat offset⌝ ∗
   ⌜bv_unsigned pointer + Z.of_nat offset < 0x40000000⌝ ∗
   writeSuccessBlobHashesLbuOuterFrame P sp pointer base total processed
     remaining bytes tail)%I.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesLbuState) := I.

Definition writeSuccessBlobHashesLbuResult `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (target : string) (index offset : nat)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (delete index writeSuccessBlobHashesBodyOtherRegShapes) ∗
   target ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) ∗
   "x19" ↦ᵣ RVal_Bits pointer ∗
   (bv_unsigned pointer + Z.of_nat offset) ↦ₘ byte ∗
   base ↦ₘ∗ take (32 * processed) bytes ∗
   bv_unsigned pointer ↦ₘ∗ take offset (drop (32 * processed) bytes) ∗
   (bv_unsigned pointer + Z.of_nat (S offset)) ↦ₘ∗
     drop (S offset) (drop (32 * processed) bytes) ∗
   ⌜drop (32 * processed) bytes !! offset = Some byte⌝ ∗
   ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
   writeSuccessBlobHashesLbuOuterFrame P sp pointer base total processed
     remaining bytes tail)%I.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesLbuResult) := I.

Lemma write_success_blob_hashes_prepare_lbu_array
    `{!islaG Sigma} (pointer : bv 64) (base : Z)
    (processed remaining offset : nat) (bytes : list (bv 8)) :
  (offset < 32)%nat ->
  base ↦ₘ∗ bytes -∗
  ⌜length bytes = (32 * (processed + S remaining))%nat⌝ -∗
  ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ -∗
  ⌜0x20000000 <= base⌝ -∗
  ⌜base + Z.of_nat (length bytes) < 0x40000000⌝ -∗
  ∃ byte : bv 8,
    (bv_unsigned pointer + Z.of_nat offset) ↦ₘ byte ∗
    base ↦ₘ∗ take (32 * processed) bytes ∗
    bv_unsigned pointer ↦ₘ∗ take offset (drop (32 * processed) bytes) ∗
    (bv_unsigned pointer + Z.of_nat (S offset)) ↦ₘ∗
      drop (S offset) (drop (32 * processed) bytes) ∗
    ⌜drop (32 * processed) bytes !! offset = Some byte⌝ ∗
    ⌜0x20000000 <= bv_unsigned pointer + Z.of_nat offset⌝ ∗
    ⌜bv_unsigned pointer + Z.of_nat offset < 0x40000000⌝.
Proof.
  intros Hoff. iIntros "Harray" (Hlength Hpointer HbaseLower HbaseUpper).
  have Hidx : (32 * processed + offset < length bytes)%nat by lia.
  iDestruct (mem_mapsto_array_region 8 base (DfracOwn 1) bytes
    (32 * processed + offset) 1 with "Harray") as
    "(Hleft & HbyteArray & Hright)".
  { lia. }
  set (byte := default (BV 8 0) (bytes !! (32 * processed + offset)%nat)).
  have HbyteLookup : bytes !! (32 * processed + offset)%nat = Some byte.
  { subst byte.
    destruct (bytes !! (32 * processed + offset)%nat) eqn:HlookupByte;
      first done.
    apply lookup_ge_None in HlookupByte. lia. }
  have HbyteTake : take 1 (drop (32 * processed + offset) bytes) = [byte].
  { assert (HdropLookup :
      (drop (32 * processed + offset) bytes) !! 0%nat = Some byte).
    { rewrite lookup_drop.
      replace (32 * processed + offset + 0)%nat
        with (32 * processed + offset)%nat by lia.
      exact HbyteLookup. }
    pose proof (take_S_r (drop (32 * processed + offset) bytes) 0 byte
      HdropLookup) as Htake.
    cbn in Htake. exact Htake. }
  iEval (rewrite HbyteTake mem_mapsto_array_singleton) in "HbyteArray".
  have HrightAddress :
      (base + Z.of_N (8 `div` 8) *
        Z.of_nat (32 * processed + offset + 1))%Z =
        (base + Z.of_nat (32 * processed + S offset))%Z.
  { replace (8 `div` 8)%N with 1%N by reflexivity. cbn. f_equal. lia. }
  have HrightDrop :
      drop (32 * processed + offset + 1) bytes =
        drop (32 * processed + S offset) bytes by (f_equal; lia).
  iEval (cbn; rewrite HrightAddress HrightDrop) in "Hright".
  have HprocessedBound : (32 * processed <= length bytes)%nat by lia.
  have Hsplit :
      take (32 * processed + offset) bytes =
        take (32 * processed) bytes ++
          take offset (drop (32 * processed) bytes).
  { rewrite take_take_drop. f_equal. }
  iAssert (base ↦ₘ∗
    (take (32 * processed) bytes ++
      take offset (drop (32 * processed) bytes)))%I with "[Hleft]"
    as "HsplitLeft".
  { rewrite -Hsplit. iExact "Hleft". }
  iDestruct (mem_mapsto_array_app 8%N base (DfracOwn 1)
    (take (32 * processed) bytes)
    (take offset (drop (32 * processed) bytes)) with "HsplitLeft") as
    "(Hdone & Hprefix)".
  have HtakeLength :
      length (take (32 * processed) bytes) = (32 * processed)%nat.
  { rewrite length_take Nat.min_l //. }
  have HcurrentAddress :
      (base + Z.of_N (8 `div` 8) * (32 * processed)%nat)%Z =
        bv_unsigned pointer.
  { rewrite Hpointer.
    change (base + 1 * Z.of_nat (32 * processed) =
      base + 32 * Z.of_nat processed)%Z.
    rewrite Nat2Z.inj_mul. lia. }
  iEval (rewrite HtakeLength HcurrentAddress) in "Hprefix".
  have HsuffixDrop :
      drop (32 * processed + S offset) bytes =
        drop (S offset) (drop (32 * processed) bytes).
  { rewrite drop_drop. f_equal. }
  iEval (rewrite HsuffixDrop) in "Hright".
  have HsuffixAddress :
      (base + Z.of_nat (32 * processed + S offset))%Z =
        (bv_unsigned pointer + Z.of_nat (S offset))%Z.
  { rewrite Hpointer Nat2Z.inj_add Nat2Z.inj_mul. lia. }
  iEval (rewrite HsuffixAddress) in "Hright".
  iRename "Hright" into "Hsuffix".
  have HbyteAddress :
      (base + Z.of_N (8 `div` 8) *
        Z.of_nat (32 * processed + offset))%Z =
        (bv_unsigned pointer + Z.of_nat offset)%Z.
  { replace (8 `div` 8)%N with 1%N by reflexivity.
    rewrite Hpointer Nat2Z.inj_add Nat2Z.inj_mul. cbn. lia. }
  iEval (cbn; rewrite HbyteAddress) in "HbyteArray".
  have HdropLookup : drop (32 * processed) bytes !! offset = Some byte.
  { rewrite lookup_drop.
    replace (offset + 32 * processed)%nat with
      (32 * processed + offset)%nat by lia.
    exact HbyteLookup. }
  have HaddressLower :
      536870912 <= bv_unsigned pointer + Z.of_nat offset.
  { rewrite Hpointer.
    have HprocessedNonnegative : (0 <= Z.of_nat processed)%Z :=
      Nat2Z.is_nonneg processed.
    have HoffsetNonnegative : (0 <= Z.of_nat offset)%Z :=
      Nat2Z.is_nonneg offset.
    nia. }
  have HaddressUpper :
      bv_unsigned pointer + Z.of_nat offset < 1073741824.
  { rewrite Hlength Nat2Z.inj_mul Nat2Z.inj_add Nat2Z.inj_succ
      in HbaseUpper.
    rewrite Hpointer.
    have HremainingNonnegative : (0 <= Z.of_nat remaining)%Z :=
      Nat2Z.is_nonneg remaining.
    apply Nat2Z.inj_lt in Hoff.
    nia. }
  iExists byte.
  iFrame "HbyteArray Hdone Hprefix Hsuffix".
  repeat iSplit; iPureIntro; assumption.
Qed.

Lemma write_success_blob_hashes_segment15_raw_frame
    `{!islaG Sigma} (pointer : bv 64) (base : Z) (processed remaining offset : nat)
    (bytes : list (bv 8)) :
  (offset < 32)%nat ->
  base ↦ₘ∗ take (32 * processed + offset) bytes -∗
  (base + Z.of_nat (32 * processed + S offset)) ↦ₘ∗
    drop (32 * processed + S offset) bytes -∗
  ⌜length bytes = (32 * (processed + S remaining))%nat⌝ -∗
  ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ -∗
  base ↦ₘ∗ take (32 * processed) bytes ∗
  bv_unsigned pointer ↦ₘ∗ take offset (drop (32 * processed) bytes) ∗
  (bv_unsigned pointer + Z.of_nat (S offset)) ↦ₘ∗
    drop (S offset) (drop (32 * processed) bytes).
Proof.
  intros Hoff. iIntros "Hleft Hright" (Hlength Hpointer).
  have HprocessedBound : (32 * processed <= length bytes)%nat by lia.
  have Hsplit :
      take (32 * processed + offset) bytes =
        take (32 * processed) bytes ++
          take offset (drop (32 * processed) bytes).
  { rewrite take_take_drop. f_equal. }
  iAssert (base ↦ₘ∗
    (take (32 * processed) bytes ++
      take offset (drop (32 * processed) bytes)))%I with "[Hleft]"
    as "HsplitLeft".
  { rewrite -Hsplit. iExact "Hleft". }
  iDestruct (mem_mapsto_array_app 8%N base (DfracOwn 1)
    (take (32 * processed) bytes)
    (take offset (drop (32 * processed) bytes)) with "HsplitLeft") as
    "(Hdone & Hprefix)".
  have HtakeLength :
      length (take (32 * processed) bytes) = (32 * processed)%nat.
  { rewrite length_take Nat.min_l //. }
  have HcurrentAddress :
      (base + Z.of_N (8 `div` 8) * (32 * processed)%nat)%Z =
        bv_unsigned pointer.
  { rewrite Hpointer.
    change (base + 1 * Z.of_nat (32 * processed) =
      base + 32 * Z.of_nat processed)%Z.
    rewrite Nat2Z.inj_mul. lia. }
  iEval (rewrite HtakeLength HcurrentAddress) in "Hprefix".
  have Hdrop :
      drop (32 * processed + S offset) bytes =
        drop (S offset) (drop (32 * processed) bytes).
  { rewrite drop_drop. f_equal. }
  iEval (rewrite Hdrop) in "Hright".
  have HrightAddress :
      (base + Z.of_nat (32 * processed + S offset))%Z =
        (bv_unsigned pointer + Z.of_nat (S offset))%Z.
  { rewrite Hpointer Nat2Z.inj_add Nat2Z.inj_mul. lia. }
  iEval (rewrite HrightAddress) in "Hright".
  iFrame "Hdone Hprefix Hright".
Qed.

Lemma write_success_blob_hashes_segment15_recombine_lbu
    `{!islaG Sigma} (pointer : bv 64) (base : Z) (processed offset : nat)
    (bytes : list (bv 8)) (byte : bv 8) :
  ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ -∗
  ⌜drop (32 * processed) bytes !! offset = Some byte⌝ -∗
  base ↦ₘ∗ take (32 * processed) bytes -∗
  (bv_unsigned pointer + Z.of_nat offset) ↦ₘ byte -∗
  bv_unsigned pointer ↦ₘ∗ take offset (drop (32 * processed) bytes) -∗
  (bv_unsigned pointer + Z.of_nat (S offset)) ↦ₘ∗
    drop (S offset) (drop (32 * processed) bytes) -∗
  base ↦ₘ∗ bytes.
Proof.
  iIntros (Hpointer Hlookup) "Hdone Hbyte Hprefix Hsuffix".
  iPoseProof (mem_mapsto_array_recombine_u8_read
    (bv_unsigned pointer) (drop (32 * processed) bytes) offset byte
    (bv_unsigned pointer + Z.of_nat (S offset))
    (bv_unsigned pointer + Z.of_nat offset) with
    "Hprefix Hsuffix Hbyte [] [] []") as "Hcurrent".
  { iPureIntro. exact Hlookup. }
  { iPureIntro. lia. }
  { iPureIntro. lia. }
  have HcurrentAddress :
      (base + Z.of_N (8 `div` 8) * (32 * processed)%nat)%Z =
        bv_unsigned pointer.
  { rewrite Hpointer.
    change (base + 1 * Z.of_nat (32 * processed) =
      base + 32 * Z.of_nat processed)%Z.
    rewrite Nat2Z.inj_mul. lia. }
  have HprocessedBound : (32 * processed <= length bytes)%nat.
  { have Hindex : (offset < length (drop (32 * processed) bytes))%nat.
    { pose proof Hlookup as Hindex.
      apply lookup_lt_Some in Hindex. exact Hindex. }
    rewrite length_drop in Hindex. lia. }
  iEval (rewrite -HcurrentAddress) in "Hcurrent".
  iPoseProof (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    (take (32 * processed) bytes) (drop (32 * processed) bytes)
    (32 * processed) with "Hdone Hcurrent") as "Harray".
  { rewrite length_take. apply Nat.min_l. exact HprocessedBound. }
  iEval (rewrite take_drop) in "Harray".
  iExact "Harray".
Qed.

Lemma write_success_blob_hashes_segment15_registers_x18
    `{!islaG Sigma} `{!threadG} (byte : bv 8) :
  reg_col (delete 16%nat writeSuccessBlobHashesBodyOtherRegShapes) -∗
  "x18" ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) -∗
  reg_col writeSuccessBlobHashesBodyOtherRegShapes.
Proof.
  iIntros "Hregs Hx18".
  rewrite (reg_col_lookup writeSuccessBlobHashesBodyOtherRegShapes 16%nat
    (KindReg "x18", BitsShape 64) ltac:(vm_compute; reflexivity)).
  iExists (RVal_Bits (bv_zero_extend 64 byte)).
  iSplit; first done. iFrame.
Qed.

Lemma write_success_blob_hashes_segment15_registers
    `{!islaG Sigma} `{!threadG} (target : string) (index : nat)
    (byte : bv 8) :
  writeSuccessBlobHashesBodyOtherRegShapes !! index =
    Some (KindReg target, BitsShape 64) ->
  reg_col (delete index writeSuccessBlobHashesBodyOtherRegShapes) -∗
  target ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) -∗
  reg_col writeSuccessBlobHashesBodyOtherRegShapes.
Proof.
  intros Hlookup. iIntros "Hregs Htarget".
  rewrite (reg_col_lookup writeSuccessBlobHashesBodyOtherRegShapes index
    (KindReg target, BitsShape 64) Hlookup).
  iExists (RVal_Bits (bv_zero_extend 64 byte)).
  iSplit; first done. iFrame.
Qed.

Lemma write_success_blob_hashes_segment15_registers_x26
    `{!islaG Sigma} `{!threadG} (byte : bv 8) :
  reg_col (delete 23%nat writeSuccessBlobHashesBodyOtherRegShapes) -∗
  "x26" ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) -∗
  reg_col writeSuccessBlobHashesBodyOtherRegShapes.
Proof.
  iIntros "Hregs Hx26".
  rewrite (reg_col_lookup writeSuccessBlobHashesBodyOtherRegShapes 23%nat
    (KindReg "x26", BitsShape 64) ltac:(vm_compute; reflexivity)).
  iExists (RVal_Bits (bv_zero_extend 64 byte)).
  iSplit; first done. iFrame.
Qed.
