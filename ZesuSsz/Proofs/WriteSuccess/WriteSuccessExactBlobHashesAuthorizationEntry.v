Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessBlobHashesSpec WriteSuccessExactAuthorizationsPrefix
  WriteSuccessExactAuthorizationsCount WriteSuccessExactTransactionsMaxBlobFeeCount
  WriteSuccessExactEncoderU128 WriteSuccessObservation WriteSuccessOutputSemantic.

Definition blobAuthorizationRemainingShapes : list (reg_kind * valu_shape) :=
  (list_delete 12%nat (list_delete 6%nat (list_delete 6%nat (list_delete 2%nat (list_delete 0%nat writeSuccessBlobHashesOtherRegShapes))))).

Definition blobAuthorizationRetained `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total : nat) (bytes : list (bv 8))
    (P : iProp Sigma) : iProp Sigma :=
  (∃ pointer : bv 64, "x19" ↦ᵣ RVal_Bits pointer ∗ "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗
   reg_col blobAuthorizationRemainingShapes ∗ base ↦ₘ∗ bytes ∗
   writeSuccessBlobHashesScratch sp ∗ ⌜bv_unsigned pointer = (base + 32 * Z.of_nat total)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobAuthorizationRetained) := I.

Definition blobAuthorizationCaller `{!islaG Sigma} `{!threadG}
    (sp low high count : bv 64) (base : Z) (total : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 144) ↦ₘ high ∗ (bv_unsigned sp + 152) ↦ₘ low ∗
   (bv_unsigned sp + 160) ↦ₘ count ∗ (bv_unsigned sp - 32) ↦ₘ? 32 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 32⌝ ∗
   ⌜bv_unsigned sp + 176 < 0x40000000⌝ ∗ P ∗
   instr_pre 0x15584 (authorizationCountPost sp count tail
     (maxBlobFeeCountFrame sp low high (blobAuthorizationRetained sp base total bytes P))) ∗ True)%I.
Global Instance : LithiumUnfold (@blobAuthorizationCaller) := I.

Lemma blob_exit_to_authorization `{!islaG Sigma} `{!threadG}
    sp base total bytes low high count tail (P : iProp Sigma) :
  writeSuccessBlobHashesLoopExit sp base total bytes
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16) (writeSuccessU128WordsPayload low high)
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail))
    (blobAuthorizationCaller sp low high count base total bytes tail P) -∗
  ∃ oldra old5 : bv 64, authorizationPrefixEntry sp low high count oldra old5 tail
    (blobAuthorizationRetained sp base total bytes P).
Proof.
  unfold writeSuccessBlobHashesLoopExit, blobAuthorizationCaller.
  iIntros "Hentry". iDestruct "Hentry" as (pointer)
    "(Hsys & Hregs & Hsp & Hptr & H22 & Hbytes & Hscratch & Hmmio & Htrace & Hcaller & %Hptr & _)".
  iDestruct "Hcaller" as "(HhighWord & HlowWord & Hcount & HcallScratch & %Halign & %Hlow & %Hhigh & HP & Hnext & _)".
  iDestruct (reg_col_lookup writeSuccessBlobHashesOtherRegShapes 0%nat (KindReg "x1", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v0 Hv0) "(Hx1 & Hregs)".
  iDestruct (reg_col_lookup (list_delete 0%nat writeSuccessBlobHashesOtherRegShapes) 2%nat (KindReg "x5", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v1 Hv1) "(Hx5 & Hregs)".
  iDestruct (reg_col_lookup (list_delete 2%nat (list_delete 0%nat writeSuccessBlobHashesOtherRegShapes)) 6%nat (KindReg "x10", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v2 Hv2) "(Hx10 & Hregs)".
  iDestruct (reg_col_lookup (list_delete 6%nat (list_delete 2%nat (list_delete 0%nat writeSuccessBlobHashesOtherRegShapes))) 6%nat (KindReg "x11", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v3 Hv3) "(Hx11 & Hregs)".
  iDestruct (reg_col_lookup (list_delete 6%nat (list_delete 6%nat (list_delete 2%nat (list_delete 0%nat writeSuccessBlobHashesOtherRegShapes)))) 12%nat (KindReg "x18", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v4 Hv4) "(Hx18 & Hregs)".
  destruct (valu_has_bits_shape _ _ Hv0) as [oldra ->].
  destruct (valu_has_bits_shape _ _ Hv1) as [old5 ->].
  iExists oldra, old5. unfold authorizationPrefixEntry.
  iFrame "Hsys Hsp Hx1 Hx5 HhighWord HlowWord Hcount HcallScratch Hmmio Htrace Hnext".
  iSplitL "Hx10 Hx11".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "Hx10"; first (iExists v2; iFrame; done).
    iSplitL "Hx11"; last done. iExists v3; iFrame; done. }
  iSplitL "Hx18".
  { rewrite reg_col_cons reg_col_nil. iSplitL "Hx18"; last done. iExists v4; iFrame; done. }
  repeat iSplit; try done. unfold blobAuthorizationRetained. iExists pointer. iFrame. done.
Qed.
Print Assumptions blob_exit_to_authorization.
