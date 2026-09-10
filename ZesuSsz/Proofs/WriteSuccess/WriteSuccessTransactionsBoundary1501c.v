From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15028.

Definition writeSuccessTransactionsAt1501cSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    "x18" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x20" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x29" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (reg_col zesu_ram_sys_regs ∗
     "x10" ↦ᵣ RVal_Bits
       (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
     "x18" ↦ᵣ RVal_Bits
       (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
         transaction 48) ∗
     "x20" ↦ᵣ RVal_Bits
       (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
         transaction 56) ∗
     "x29" ↦ᵣ RVal_Bits
       (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
         transaction 64) -∗
     writeSuccessTransactionsMachine15028
       sp base transactions processed transaction) ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt1501cSpec) := I.
