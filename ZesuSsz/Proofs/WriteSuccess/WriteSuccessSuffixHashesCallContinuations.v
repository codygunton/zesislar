Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes1574cCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15750Branch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesBranchAdapters.

Definition writeSuccessSuffixHashes15750NonzeroQ
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma) : iProp Sigma :=
  ("x1" ↦ᵣ RVal_Bits (BV 64 0x15750) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ Q)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashes15750NonzeroQ) := I.

Definition writeSuccessSuffixHashes15750ZeroQ
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (tail : spec) (Q : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixHashes15750NonzeroQ sp (BV 64 0) tail Q.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashes15750ZeroQ) := I.

Lemma write_success_suffix_hashes_15750_nonzero_call_continuation
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma)
    (Hvalue : value <> BV 64 0) :
  instr_body 0x15750
    (writeSuccessSuffixHashes15750NonzeroState value
      (writeSuccessSuffixHashes15750NonzeroQ sp value tail Q)) -∗
  (writeSuccessSuffixHashes1574cCallPost sp value tail ∗
   "x8" ↦ᵣ RVal_Bits value ∗ Q) -∗
  instr_pre 0x15750
    (writeSuccessSuffixHashes1574cCallPost sp value tail ∗
     "x8" ↦ᵣ RVal_Bits value ∗ Q).
Proof.
  iIntros "Hnext Hframe".
  iApply (write_success_suffix_hashes_15750_nonzero_pre_adapter
    value (writeSuccessSuffixHashes15750NonzeroQ sp value tail Q)
    (writeSuccessSuffixHashes1574cCallPost sp value tail ∗
      "x8" ↦ᵣ RVal_Bits value ∗ Q) Hvalue).
  - iIntros "Hstate".
    iDestruct "Hstate" as "(Hcall & H8 & HQ)".
    iEval (unfold writeSuccessSuffixHashes15750NonzeroQ) in "HQ".
    iEval (unfold writeSuccessSuffixHashes1574cCallPost) in "Hcall".
    iDestruct "Hcall" as
      "(Hsys & Hx1 & Hx2 & Hx5 & Hx10 & Hx11 & Hstack & Hmmio & Htrace & _)".
    have H15750 : Z_to_bv 64 0x15750 = BV 64 0x15750 by bv_solve.
    rewrite /writeSuccessSuffixHashes15750NonzeroState.
    rewrite /writeSuccessSuffixHashes15750NonzeroQ.
    rewrite <- H15750.
    iFrame.
  - iExact "Hnext".
Qed.

Lemma write_success_suffix_hashes_15750_zero_call_continuation
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (tail : spec) (Q : iProp Sigma) :
  instr_body 0x15750
    (writeSuccessSuffixHashes15750ZeroState
      (writeSuccessSuffixHashes15750ZeroQ sp tail Q)) -∗
  (writeSuccessSuffixHashes1574cCallPost sp (BV 64 0) tail ∗
   "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗ Q) -∗
  instr_pre 0x15750
    (writeSuccessSuffixHashes1574cCallPost sp (BV 64 0) tail ∗
     "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗ Q).
Proof.
  iIntros "Hnext Hframe".
  iApply (write_success_suffix_hashes_15750_zero_pre_adapter
    (writeSuccessSuffixHashes15750ZeroQ sp tail Q)
    (writeSuccessSuffixHashes1574cCallPost sp (BV 64 0) tail ∗
      "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗ Q)).
  - iIntros "Hstate".
    iDestruct "Hstate" as "(Hcall & H8 & HQ)".
    iEval (unfold writeSuccessSuffixHashes15750ZeroQ) in "HQ".
    iEval (unfold writeSuccessSuffixHashes1574cCallPost) in "Hcall".
    iDestruct "Hcall" as
      "(Hsys & Hx1 & Hx2 & Hx5 & Hx10 & Hx11 & Hstack & Hmmio & Htrace & _)".
    have H15750 : Z_to_bv 64 0x15750 = BV 64 0x15750 by bv_solve.
    iEval (rewrite H15750) in "Hx1".
    rewrite /writeSuccessSuffixHashes15750ZeroState.
    cbn [writeSuccessSuffixHashes15750ZeroQ
      writeSuccessSuffixHashes15750NonzeroQ].
    iFrame.
  - iExact "Hnext".
Qed.
