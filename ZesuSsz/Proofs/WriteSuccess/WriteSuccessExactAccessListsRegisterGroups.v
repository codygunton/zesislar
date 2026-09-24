Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Definition accessUnchangedRegisters : list string :=
  ["x3"; "x4"; "x6"; "x7"; "x8"; "x9"; "x16"; "x17"; "x18";
   "x20"; "x21"; "x23"; "x24"; "x25"; "x26"; "x28"; "x29"; "x30"; "x31"].
Definition accessRegisterGroup `{!islaG Sigma} `{!threadG}
    (registers : list string) : iProp Sigma :=
  reg_col ((λ register, (KindReg register, BitsShape 64)) <$> registers).
Global Instance : LithiumUnfold (@accessRegisterGroup) := I.

Lemma access_copy_register_groups `{!islaG Sigma} `{!threadG} :
  reg_col writeSuccessAccessListsOtherRegShapes -∗
  ∃ old_ra old5 : bv 64,
    "x1" ↦ᵣ RVal_Bits old_ra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
    accessRegisterGroup ["x12"; "x13"; "x14"; "x15"] ∗
    accessRegisterGroup accessUnchangedRegisters ∗ True.
Proof. move => *. zesu_block. Qed.
Print Assumptions access_copy_register_groups.
