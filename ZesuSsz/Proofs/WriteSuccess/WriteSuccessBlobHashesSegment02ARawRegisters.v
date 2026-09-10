Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.

Lemma write_success_blob_hashes_segment02_raw_registers
    `{!islaG Sigma} `{!threadG} (byte : bv 8) :
  reg_col (delete 24%nat writeSuccessBlobHashesOtherRegShapes) -∗
  "x28" ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) -∗
  reg_col writeSuccessBlobHashesOtherRegShapes.
Proof.
  iIntros "Hregs Hx28".
  rewrite (reg_col_lookup writeSuccessBlobHashesOtherRegShapes 24%nat
    (KindReg "x28", BitsShape 64) ltac:(vm_compute; reflexivity)).
  iExists (RVal_Bits (bv_zero_extend 64 byte)).
  iSplit; first done. iFrame.
Qed.
