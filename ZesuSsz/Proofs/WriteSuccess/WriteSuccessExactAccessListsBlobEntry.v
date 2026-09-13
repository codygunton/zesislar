Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAccessListsReturnLoopEntry WriteSuccessExactAccessListsReturnCount
  WriteSuccessExactEncoderIntFramedCall WriteSuccessExactAccessListsBlobRegisters
  WriteSuccessExactBlobHashesHeader WriteSuccessBlobHashesSpec
  WriteSuccessAccessListsSpec WriteSuccessStorageKeysSpec WriteSuccessExactBlobHashesModel.

Definition accessBlobReturnedMemory `{!islaG Sigma} `{!threadG}
    (sp savedX22 : bv 64) (accessBase : Z) (entries : list writeSuccessAccessEntry)
    (accessBytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (∃ storedIndex : bv 64,
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ (bv_unsigned sp + 136) ↦ₘ savedX22 ∗
   accessBase ↦ₘ∗ accessBytes ∗ writeSuccessAccessEntriesOwn entries ∗
   (bv_unsigned sp + 256) ↦ₘ Z_to_bv 64 accessBase ∗
   (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat (length entries)) ∗
   (bv_unsigned sp + 272) ↦ₘ storedIndex ∗ (bv_unsigned sp + 1744) ↦ₘ? 40 ∗
   writeSuccessStorageKeysScratch sp ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessBlobReturnedMemory) := I.

Definition accessBlobSourceResources `{!islaG Sigma} `{!threadG}
    (sp pointer savedX22 : bv 64) (base : Z) (total : nat) (bytes : list (bv 8))
    (tail : spec) (F : iProp Sigma) : iProp Sigma :=
  (base ↦ₘ∗ bytes ∗ writeSuccessBlobHashesScratch sp ∗
   ⌜length bytes = (32 * total)%nat⌝ ∗ ⌜bv_unsigned pointer = base⌝ ∗
   ⌜savedX22 = Z_to_bv 64 (Z.of_nat total)⌝ ∗
   ⌜(Z.of_nat total < 18446744073709551616)%Z⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
   instr_pre 0x15564 (writeSuccessBlobHashesLoopExit sp base total bytes tail F) ∗ True)%I.
Global Instance : LithiumUnfold (@accessBlobSourceResources) := I.

Lemma access_return_to_blob_entry `{!islaG Sigma} `{!threadG}
    sp pointer savedX22 accessBase entries accessBytes base total bytes tail (P : iProp Sigma) :
  accessReturnCountPost sp savedX22 (writeSuccessExactBlobHashesEvents sp 0 total bytes tail)
    (accessReturnLoopFrame sp accessBase entries accessBytes pointer
      (accessBlobSourceResources sp pointer savedX22 base total bytes tail
        (accessBlobReturnedMemory sp savedX22 accessBase entries accessBytes P) ∗ P ∗ True)) -∗
  blobHeaderEntry sp pointer base total bytes tail
    (accessBlobReturnedMemory sp savedX22 accessBase entries accessBytes P).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hstack & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(H22 & Hsaved & Hloop & _)".
  iDestruct "Hloop" as (storedIndex old27)
    "(Htmp & Hother & H19 & H27 & Haccess & Hown & Hbase & Htotal & Hindex & Hcopied & Hkeys & Hbounds & _)".
  iDestruct "Hbounds" as "(%Halign & %Hlow & %Hhigh & Hresources & _)".
  iDestruct "Hresources" as "(Hsource & HP & _)".
  iDestruct "Hsource" as
    "(Hbytes & Hscratch & %Hlen & %Hptr & %Hcount & %Hbound & %HsrcLow & %HsrcHigh & Hnext & _)".
  iPoseProof (access_blob_registers with "[$H1 $H5 $H10 $H11 $H27 $Htmp $Hother]") as "Hregs".
  subst savedX22. unfold blobHeaderEntry.
  iFrame "Hsys Hregs Hsp H19 H22 Hbytes Hscratch Hmmio Htrace Hnext".
  iSplitL "Hstack Hsaved Haccess Hown Hbase Htotal Hindex Hcopied Hkeys HP".
  { unfold accessBlobReturnedMemory. iExists storedIndex. iFrame. }
  repeat iSplit; try done. iPureIntro. clear -Hlow. lia.
Qed.
Print Assumptions access_return_to_blob_entry.
