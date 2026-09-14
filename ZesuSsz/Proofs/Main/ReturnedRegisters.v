Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.

Definition mainReturnedOtherRegisters `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (reg_col ((fun register => (KindReg register, BitsShape 64)) <$> ["x3"; "x4"]) ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x7"; "x13"; "x14"; "x15"; "x16"; "x17"; "x28"; "x29"; "x30"; "x31"]))%I.

Lemma main_returned_other_registers `{!islaG Sigma} `{!threadG} :
  reg_col writeSuccessOtherRegShapes ⊢
  ∃ x5 x6 : bv 64, "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ mainReturnedOtherRegisters.
Proof.
  rewrite /writeSuccessOtherRegShapes /writeSuccessOtherRegisters /= !reg_col_cons /=.
  iIntros "(H3&H4&H5&H6&Hrest)".
  iDestruct "H5" as (v5) "[%Hshape5 H5]".
  iDestruct "H6" as (v6) "[%Hshape6 H6]".
  destruct (valu_has_bits_shape _ _ Hshape5) as [x5 ->].
  destruct (valu_has_bits_shape _ _ Hshape6) as [x6 ->].
  iExists x5, x6.
  rewrite /mainReturnedOtherRegisters /= !reg_col_cons /=.
  iFrame. rewrite reg_col_nil. done.
Qed.
Print Assumptions main_returned_other_registers.
