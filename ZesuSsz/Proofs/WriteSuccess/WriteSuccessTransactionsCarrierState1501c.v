Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15028.

Definition writeSuccessTransactionsAt1501cCarrierSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    reg_col zesu_ram_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    "x18" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x20" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x29" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (reg_col zesu_ram_sys_regs ∗
     "x10" ↦ᵣ RVal_Bits
       (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
     "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
     "x20" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
     "x29" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 64) -∗
     writeSuccessTransactionsMachine15028Carrier
       sp base transactions processed transaction
       first second third fourth items) ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt1501cCarrierSpec) := I.
