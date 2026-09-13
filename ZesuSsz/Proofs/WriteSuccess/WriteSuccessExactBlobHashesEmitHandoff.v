Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesWide WriteSuccessExactStorageKeysWords
  WriteSuccessExactBlobHashesEmit WriteSuccessExactStorageKeysPayloadWords.

Definition blobOutputResources `{!islaG Sigma} `{!threadG}
    (sp a b c d : bv 64) (key : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗
   reg_col [(KindReg "x1", BitsShape 64)] ∗
   (bv_unsigned sp + 1680) ↦ₘ a ∗ (bv_unsigned sp + 1688) ↦ₘ b ∗
   (bv_unsigned sp + 1696) ↦ₘ c ∗ (bv_unsigned sp + 1704) ↦ₘ d ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1680)%bv (BV 64 32) key tail) ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1712 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobOutputResources) := I.

Definition blobEmitCallerFrame `{!islaG Sigma} `{!threadG}
    (row count : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col ((λ r, (KindReg r, BitsShape 64)) <$>
     ["x6"; "x7"; "x8"; "x9"; "x15"; "x16"; "x17"; "x18";
      "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x28"; "x29"; "x30"; "x31"]) ∗
   blobWordFrame row count base bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@blobEmitCallerFrame) := I.

Definition blobWideRegisterShapes : list (reg_kind * valu_shape) :=
  (λ r, (KindReg r, BitsShape 64)) <$>
    ["x5"; "x6"; "x7"; "x8"; "x9"; "x11"; "x15"; "x16"; "x17"; "x18";
     "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x28"; "x29"; "x30"; "x31"].

Lemma blob_wide_to_emit `{!islaG Sigma} `{!threadG}
    row count base bytes index sp a b c d tail (P : iProp Sigma) :
  blobWidePost row count base bytes index
    (blobOutputResources sp a b c d (take 32 (drop index bytes)) tail P) -∗
  ∃ old_ra old5 old11 : bv 64,
    blobEmitEntry sp old_ra old5 old11 a b c d (take 32 (drop index bytes)) tail
      (blobEmitCallerFrame row count base bytes index P).
Proof.
  iIntros "Hwide".
  iEval (unfold blobWidePost, blobWordFrame) in "Hwide".
  iDestruct "Hwide" as
    "(Hsys & H14 & H12 & H13 & H10 & Hregs & (Hrow & Hcount & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh & Houtput & _) & _)".
  iDestruct (reg_col_lookup blobWideRegisterShapes 0 (KindReg "x5", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v5 Hv5) "(H5 & Hregs)".
  iDestruct (reg_col_lookup (list_delete 0%nat blobWideRegisterShapes) 4 (KindReg "x11", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v11 Hv11) "(H11 & Hregs)".
  destruct (valu_has_bits_shape _ _ Hv5) as [old5 ->].
  destruct (valu_has_bits_shape _ _ Hv11) as [old11 ->].
  iEval (unfold blobOutputResources) in "Houtput".
  iDestruct "Houtput" as
    "(Hsp & Hra & Ha & Hb & Hc & Hd & Hmmio & Htrace & %Halign & %Hsplow & %Hsphigh & HP & _)".
  iDestruct (reg_col_lookup [(KindReg "x1", BitsShape 64)] 0 (KindReg "x1", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hra") as (v1 Hv1) "(H1 & _)".
  destruct (valu_has_bits_shape _ _ Hv1) as [old_ra ->].
  iExists old_ra, old5, old11.
  iEval (unfold blobEmitEntry, blobEmitFrame,
    blobEmitCallerFrame, blobWordFrame).
  iEval (rewrite
    (storage_keys_payload_word bytes index 0 Hbound ltac:(lia))
    (storage_keys_payload_word bytes index 8 Hbound ltac:(lia))
    (storage_keys_payload_word bytes index 16 Hbound ltac:(lia))
    (storage_keys_payload_word bytes index 24 Hbound ltac:(lia))).
  iFrame. iPureIntro. rewrite length_take length_drop. lia.
Qed.
Print Assumptions blob_wide_to_emit.
