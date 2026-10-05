Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation.Switches.RamFault.
Open Scope Z_scope.
Lemma stack_low_upper `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (returnAddress : Z) (resources : iProp Sigma) es
    (Hdomain : decodeItemDomainAt returnAddress decodeItemC1BDomain args) :
  resources -∗ (WPasm (Smt (Assert (Unop Not
    (Val (Val_Bool (bool_decide (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600 + 0) + 8) <= bv_signed (BV 128 3221225472)))) Mk_annot) Mk_annot)) Mk_annot :t: es) ∧ True).
Proof.
  iStartProof. iIntros "Hresources".
  lazymatch goal with |- context[bool_decide ?bound] =>
    set (faultDecision := bool_decide bound)
  end.
  zesu_ram_fault_if_enabled.
Qed.
Lemma stack_low_lower `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (returnAddress : Z) (resources : iProp Sigma) es
    (Hdomain : decodeItemDomainAt returnAddress decodeItemC1BDomain args) :
  resources -∗ (WPasm (Smt (Assert (Unop Not
    (Val (Val_Bool (bool_decide (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600 + 0)) >= bv_signed (BV 128 2684354560)))) Mk_annot) Mk_annot)) Mk_annot :t: es) ∧ True).
Proof.
  iStartProof. iIntros "Hresources".
  lazymatch goal with |- context[bool_decide ?bound] =>
    set (faultDecision := bool_decide bound)
  end.
  zesu_ram_fault_if_enabled.
Qed.
Lemma stack_high_upper `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (returnAddress : Z) (resources : iProp Sigma) es
    (Hdomain : decodeItemDomainAt returnAddress decodeItemC1BDomain args) :
  resources -∗ (WPasm (Smt (Assert (Unop Not
    (Val (Val_Bool (bool_decide (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600 + 8) + 8) <= bv_signed (BV 128 3221225472)))) Mk_annot) Mk_annot)) Mk_annot :t: es) ∧ True).
Proof.
  iStartProof. iIntros "Hresources".
  lazymatch goal with |- context[bool_decide ?bound] =>
    set (faultDecision := bool_decide bound)
  end.
  zesu_ram_fault_if_enabled.
Qed.
Lemma stack_high_lower `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (returnAddress : Z) (resources : iProp Sigma) es
    (Hdomain : decodeItemDomainAt returnAddress decodeItemC1BDomain args) :
  resources -∗ (WPasm (Smt (Assert (Unop Not
    (Val (Val_Bool (bool_decide (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600 + 8)) >= bv_signed (BV 128 2684354560)))) Mk_annot) Mk_annot)) Mk_annot :t: es) ∧ True).
Proof.
  iStartProof. iIntros "Hresources".
  lazymatch goal with |- context[bool_decide ?bound] =>
    set (faultDecision := bool_decide bound)
  end.
  zesu_ram_fault_if_enabled.
Qed.
