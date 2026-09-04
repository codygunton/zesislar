Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSpec.

Lemma write_success_access_lists_storage_registers
    `{!islaG Sigma} `{!threadG} (x10 x11 : bv 64) :
  reg_col writeSuccessAccessListsOtherRegShapes -∗
  "x10" ↦ᵣ RVal_Bits x10 -∗
  "x11" ↦ᵣ RVal_Bits x11 -∗
  reg_col writeSuccessStorageKeysOtherRegShapes.
Proof.
  iIntros "Hregs Hx10 Hx11".
  iEval (rewrite /reg_col; cbn) in "Hregs".
  iDestruct "Hregs" as
    "(H1 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H12 & H13 & H14 &
      H15 & H16 & H17 & H18 & H20 & H21 & H23 & H24 & H25 & H26 &
      H28 & H29 & H30 & H31 & _)".
  rewrite /reg_col. cbn.
  iFrame.
  all: done.
Qed.
