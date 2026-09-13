Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsReturnCount.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsRegisterGroups.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Export.Snapshots.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Definition accessReturnRuntimeBounds `{!islaG Sigma}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessReturnRuntimeBounds) := I.

Definition accessReturnLoopFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (entries : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (x19 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ storedIndex old27 : bv 64,
   accessRegisterGroup ["x12"; "x13"; "x14"; "x15"] ∗
   accessRegisterGroup accessUnchangedRegisters ∗ "x19" ↦ᵣ RVal_Bits x19 ∗
   "x27" ↦ᵣ RVal_Bits old27 ∗ base ↦ₘ∗ bytes ∗ writeSuccessAccessEntriesOwn entries ∗
   (bv_unsigned sp + 256) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat (length entries)) ∗
   (bv_unsigned sp + 272) ↦ₘ storedIndex ∗
   (bv_unsigned sp + 1744) ↦ₘ? 40 ∗ writeSuccessStorageKeysScratch sp ∗
   accessReturnRuntimeBounds sp P ∗ True)%I.
Global Instance : LithiumUnfold (@accessReturnLoopFrame) := I.

Lemma access_return_loop_entry_resources `{!islaG Sigma} `{!threadG}
    sp base entries bytes x19 savedX22 tail (P : iProp Sigma) :
  (writeSuccessAccessListsLoopExit sp base entries bytes
     (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail)
     x19 savedX22 (accessReturnRuntimeBounds sp P) ∗
   instr_pre 0x153d0 (accessReturnCountPost sp savedX22 tail
     (accessReturnLoopFrame sp base entries bytes x19 P)) ∗ True)%I -∗
  ∃ old22 old_ra old5 : bv 64,
    accessReturnCountEntry sp savedX22 old22 old_ra old5
      (Z_to_bv 64 (Z.of_nat (length entries))) (Z_to_bv 64 (Z.of_nat (length entries))) tail
      (accessReturnLoopFrame sp base entries bytes x19 P).
Proof.
  iIntros "(Hpost & Hnext & _)". iDestruct "Hpost" as (storedIndex old22 old27)
    "(Hsys & Hregs & Hsp & H19 & Hdata & Hsize & H22 & H27 & Hbytes & Hown &
     Hscratch & Hmmio & Htrace & Hbounds & _)".
  iDestruct "Hbounds" as "(%Halign & %Hlow & %Hhigh & HP & _)".
  iDestruct (access_copy_register_groups with "Hregs") as (old_ra old5)
    "(Hra & H5 & Htmp & Hregs & _)".
  iDestruct "Hscratch" as "(Hsaved & Hbase & Htotal & Hindex & Hcopied & Hstack & Hkeyscratch & _)".
  iExists old22, old_ra, old5. unfold accessReturnCountEntry.
  iFrame "Hsys Hsp H22 Hra H5 Hdata Hsize Hsaved Hstack Hmmio Htrace Hnext".
  iSplit; first done. iSplit; first done.
  iSplit; first (iPureIntro; clear -Hhigh; lia).
  iSplit; last done. unfold accessReturnLoopFrame. iExists storedIndex, old27.
  unfold accessReturnRuntimeBounds. iFrame. repeat iSplit; done.
Qed.
Print Assumptions access_return_loop_entry_resources.
