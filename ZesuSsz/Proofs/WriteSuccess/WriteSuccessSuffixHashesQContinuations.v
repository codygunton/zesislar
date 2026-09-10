Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes1574cCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Definition writeSuccessSuffixHashes15748Q
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma) : iProp Sigma :=
  ("x8" ↦ᵣ RVal_Bits value ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ: (fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
   "x10" ↦ᵣ RVal_Bits value ∗
   "x11" ↦ᵣ: (fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp < 0x40000000⌝ ∗ Q)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashes15748Q) := I.

Lemma write_success_suffix_hashes_q15748
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15748) ∗
   writeSuccessSuffixHashes15748Q sp value tail
     (instr_pre 0x15750
       (writeSuccessSuffixHashes1574cCallPost sp value tail) ∗ Q)) -∗
  writeSuccessSuffixHashes1574cCallSpec ("x8" ↦ᵣ RVal_Bits value ∗ Q).
Proof.
  iIntros "(Hsys & H1 & Hrest)".
  rewrite /writeSuccessSuffixHashes15748Q.
  iDestruct "Hrest" as "(H8 & H2 & H5 & H10 & H11 & Hstack & Hmmio &
    Htrace & %Halign & %Hmin & %Hmax & Hret & HQ)".
  rewrite /writeSuccessSuffixHashes1574cCallSpec.
  iExists sp, value, tail.
  iFrame "Hsys H1 H8 H2 H5 H10 H11 Hstack Hmmio Htrace Hret HQ".
  iPureIntro; repeat split; assumption.
Qed.

Definition writeSuccessSuffixHashes15744Q
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma) : iProp Sigma :=
  ("x1" ↦ᵣ: (fun r1 => ⌜valu_has_shape r1 (BitsShape 64)⌝) ∗ Q)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashes15744Q) := I.

Lemma write_success_suffix_hashes_q15744
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits value ∗
   "x10" ↦ᵣ RVal_Bits value ∗
   writeSuccessSuffixHashes15744Q sp value tail
     (writeSuccessSuffixHashes15748Q sp value tail Q)) -∗
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ: (fun r1 => ⌜valu_has_shape r1 (BitsShape 64)⌝) ∗
   writeSuccessSuffixHashes15748Q sp value tail Q).
Proof.
  iIntros "(Hsys & H8 & H10 & Hrest)".
  iEval (rewrite /writeSuccessSuffixHashes15744Q) in "Hrest".
  iDestruct "Hrest" as "(H1 & Hrest)".
  iFrame.
Qed.
