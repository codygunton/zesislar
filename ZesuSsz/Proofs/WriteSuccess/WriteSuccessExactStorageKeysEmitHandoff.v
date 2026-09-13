Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysWide WriteSuccessExactStorageKeysWords
  WriteSuccessExactStorageKeysEmit WriteSuccessExactStorageKeysPayloadWords.

Definition storageKeysOutputResources `{!islaG Sigma} `{!threadG}
    (sp a b c d : bv 64) (key : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1712) ↦ₘ a ∗ (bv_unsigned sp + 1720) ↦ₘ b ∗
   (bv_unsigned sp + 1728) ↦ₘ c ∗ (bv_unsigned sp + 1736) ↦ₘ d ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1712)%bv (BV 64 32) key tail) ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1744 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysOutputResources) := I.

Definition storageKeysEmitCallerFrame `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col ((λ r, (KindReg r, BitsShape 64)) <$>
     ["x24"; "x25"; "x26"; "x18"; "x23"; "x31"; "x30"; "x29";
      "x16"; "x8"; "x21"; "x20"; "x9"; "x7"; "x28";
      "x17"; "x6"; "x15"]) ∗
   storageKeysWordFrame row base bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysEmitCallerFrame) := I.

Definition storageKeysWideRegisterShapes : list (reg_kind * valu_shape) :=
  (λ r, (KindReg r, BitsShape 64)) <$>
    ["x24"; "x25"; "x26"; "x1"; "x18"; "x23"; "x31"; "x30"; "x29";
     "x16"; "x8"; "x21"; "x20"; "x9"; "x7"; "x28";
     "x17"; "x5"; "x6"; "x15"; "x11"].

Lemma storage_keys_wide_to_emit `{!islaG Sigma} `{!threadG}
    row base bytes index sp a b c d tail (P : iProp Sigma) :
  storageKeysWidePost row base bytes index
    (storageKeysOutputResources sp a b c d (take 32 (drop index bytes)) tail P) -∗
  ∃ old_ra old5 old11 : bv 64,
    storageKeysEmitEntry sp old_ra old5 old11 a b c d (take 32 (drop index bytes)) tail
      (storageKeysEmitCallerFrame row base bytes index P).
Proof.
  iIntros "Hwide".
  iEval (unfold storageKeysWidePost, storageKeysWordFrame) in "Hwide".
  iDestruct "Hwide" as
    "(Hsys & H14 & H12 & H13 & H10 & Hregs & (Hrow & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh & Houtput & _) & _)".
  iDestruct (reg_col_lookup storageKeysWideRegisterShapes 3 (KindReg "x1", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v1 Hv1) "(H1 & Hregs)".
  iDestruct (reg_col_lookup (list_delete 3%nat storageKeysWideRegisterShapes) 16 (KindReg "x5", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v5 Hv5) "(H5 & Hregs)".
  iDestruct (reg_col_lookup (list_delete 16%nat (list_delete 3%nat storageKeysWideRegisterShapes)) 18 (KindReg "x11", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v11 Hv11) "(H11 & Hregs)".
  destruct (valu_has_bits_shape _ _ Hv1) as [old_ra ->].
  destruct (valu_has_bits_shape _ _ Hv5) as [old5 ->].
  destruct (valu_has_bits_shape _ _ Hv11) as [old11 ->].
  iEval (unfold storageKeysOutputResources) in "Houtput".
  iDestruct "Houtput" as
    "(Hsp & Ha & Hb & Hc & Hd & Hmmio & Htrace & %Halign & %Hsplow & %Hsphigh & HP & _)".
  iExists old_ra, old5, old11.
  iEval (unfold storageKeysEmitEntry, storageKeysEmitFrame,
    storageKeysEmitCallerFrame, storageKeysWordFrame).
  iEval (rewrite
    (storage_keys_payload_word bytes index 0 Hbound ltac:(lia))
    (storage_keys_payload_word bytes index 8 Hbound ltac:(lia))
    (storage_keys_payload_word bytes index 16 Hbound ltac:(lia))
    (storage_keys_payload_word bytes index 24 Hbound ltac:(lia))).
  iFrame. iPureIntro. rewrite length_take length_drop. lia.
Qed.
Print Assumptions storage_keys_wide_to_emit.
