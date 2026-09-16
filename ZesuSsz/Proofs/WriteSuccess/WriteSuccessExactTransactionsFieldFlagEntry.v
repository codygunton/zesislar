Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.RegPacking.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFieldLoads WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactTransactionsGasLoads.

Definition transactionFieldFlagCaller `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   ⌜(index + 283 <= length bytes)%nat⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionFieldFlagCaller) := I.

Definition transactionFieldFlagRetained `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowWord bytes index 160) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowWord bytes index 168) ∗
   "x26" ↦ᵣ RVal_Bits (transactionRowWord bytes index 184) ∗
   "x8" ↦ᵣ RVal_Bits (transactionRowWord bytes index 192) ∗
   (bv_unsigned sp + 272) ↦ₘ (transactionRowWord bytes index 176) ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 280 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionFieldFlagRetained) := I.

Lemma transactions_field_flag_entry `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  transactionFieldLoadPost sp row base bytes index (transactionFieldFlagCaller bytes index P) -∗
  transactionFlagLoadEntry row base bytes index (transactionFieldFlagRetained sp bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionFieldLoadPost) in "Hpost".
  iDestruct "Hpost" as "(Hsys & H11 & H12 & H13 & H26 & H8 & Hsp & Hrow & Hbytes &
    Hnonce & %Hcursor & %Hlength & %Hrowalign & %Hmin & %Hmax & %Hspalign &
    %Hspmin & %Hspmax & Hcaller & _)".
  iEval (rewrite /transactionFieldFlagCaller) in "Hcaller".
  iDestruct "Hcaller" as "(Hflags & %HflagsLength & HP & _)".
  iAssert (reg_col [(KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64);
    (KindReg "x15", BitsShape 64)])%I with "[H13 Hflags]" as "Hregs".
  { iApply (reg_col_mixed_collect [("x13", transactionRowWord bytes index 176)] []
      [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)]).
    - solve_Permutation.
    - iFrame. rewrite big_sepL_nil reg_col_nil. done. }
  rewrite /transactionFlagLoadEntry /transactionFieldFlagRetained.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_field_flag_entry.
