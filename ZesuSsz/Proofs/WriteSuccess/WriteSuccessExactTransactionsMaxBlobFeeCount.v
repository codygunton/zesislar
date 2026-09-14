Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CallScratchSized.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsMaxBlobFee WriteSuccessExactEncoderU128
  WriteSuccessExactAuthorizationsCount.

Definition maxBlobFeeCountFrame `{!islaG Sigma} `{!threadG}
    (sp low high : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp - 32) ↦ₘ? 16 ∗
   (bv_unsigned sp + 144) ↦ₘ high ∗ (bv_unsigned sp + 152) ↦ₘ low ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 32⌝ ∗
   ⌜bv_unsigned sp + 176 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@maxBlobFeeCountFrame) := I.

Lemma max_blob_fee_to_count `{!islaG Sigma} `{!threadG}
    (sp low high count : bv 64) tail (P : iProp Sigma) :
  (maxBlobFeePost sp low high
     (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail)
     (reg_col [(KindReg "x18", BitsShape 64)] ∗
      (bv_unsigned sp + 160) ↦ₘ count ∗
      ⌜bv_unsigned sp + 176 < 0x40000000⌝ ∗ P ∗ True)%I ∗
   instr_pre 0x15584 (authorizationCountPost sp count tail (maxBlobFeeCountFrame sp low high P)) ∗ True)%I -∗
  authorizationCountEntry sp count (BV 64 0x15574) (BV 64 0x2401a0b8)
    (BV 64 16) tail (maxBlobFeeCountFrame sp low high P).
Proof.
  iIntros "(Hpost & Hnext & _)".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hpayload & Hgap & Hret & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hhighword & Hlowword & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(H18 & Hcount & %Hhigh176 & HP & _)".
  have Hlen : length (writeSuccessU128WordsPayload low high) = N.to_nat 16 by reflexivity.
  have Hoffset : (sp - Z_to_bv 64 (Z.of_N 16 + 16))%bv = (sp - BV 64 32)%bv by bv_solve.
  iEval (rewrite -Hoffset) in "Hpayload".
  iPoseProof (call_scratch_reuse_sized sp (BV 64 0x15574) _ 16 Hlen Hlow
    with "[$Hpayload $Hgap $Hret]") as "Hscratch".
  iDestruct (mem_mapsto_uninit_split 16 with "Hscratch") as "[Hlower Hupper]"; first lia.
  iEval (replace (bv_unsigned sp - 32 + 16)%Z with (bv_unsigned sp - 16)%Z by lia) in "Hupper".
  unfold authorizationCountEntry.
  iFrame "Hsys Hsp H1 H5 H11 Hcount Hupper Hmmio Htrace Hnext".
  iSplitL "H10 H18".
  { rewrite reg_col_cons. iSplitL "H10"; last iExact "H18". iExists _. iFrame. done. }
  iSplit; first done. iSplit; first (iPureIntro; lia). iSplit; first done.
  unfold maxBlobFeeCountFrame. iFrame. repeat iSplit; done.
Qed.
Print Assumptions max_blob_fee_to_count.
