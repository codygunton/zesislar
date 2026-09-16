Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.

Lemma write_success_blob_hashes_segment17_registers_x22
    `{!islaG Sigma} `{!threadG} (byte : bv 8) :
  reg_col (delete 19%nat writeSuccessBlobHashesBodyOtherRegShapes) -∗
  "x22" ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) -∗
  reg_col writeSuccessBlobHashesBodyOtherRegShapes.
Proof.
  iIntros "Hregs Hx22".
  rewrite (reg_col_lookup writeSuccessBlobHashesBodyOtherRegShapes 19%nat
    (KindReg "x22", BitsShape 64) ltac:(vm_compute; reflexivity)).
  iExists (RVal_Bits (bv_zero_extend 64 byte)).
  iSplit; first done. iFrame.
Qed.
