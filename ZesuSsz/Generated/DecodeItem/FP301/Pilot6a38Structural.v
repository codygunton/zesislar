(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Local Open Scope Z_scope.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a38Entries.
#[export] Instance fp_machineAt6a38_LoopExit_unfold : LithiumUnfold (@fp_machineAt6a38_LoopExit) := I.
#[export] Typeclasses Opaque fp_machineAt6a38_LoopExit.
#[export] Instance fp_machineAt6a38_LoopExit_intro `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt6a38_LoopExit (args) (returnAddress))
  (∃ (machine_x13 : bv 64) (machine_x15 : bv 64) (machine_x16 : bv 64) (machine_x11 : bv 64) (i : lvar "zesuLoopIndex" Z), (reg_col (decodeItemSysRegs args) ∗ "x10" ↦ᵣ RVal_Bits (((Z_to_bv 64%N (decodeItemOutputPointer args))) : bv 64%N) ∗ "x11" ↦ᵣ RVal_Bits (machine_x11 : bv 64%N) ∗ "x12" ↦ᵣ RVal_Bits (((Z_to_bv 64%N (decodeItemInputLength args))) : bv 64%N) ∗ "x13" ↦ᵣ RVal_Bits (machine_x13 : bv 64%N) ∗ "x14" ↦ᵣ RVal_Bits ((bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64%N (List.nth 0%nat (decodeItemInputBytes args) (BV 8%N 0%Z))) (BV 64%N 255%Z)) (BV 64%N 73%Z)) (BV 64%N 255%Z)) (BV 64%N 1%Z)) : bv 64%N) ∗ "x15" ↦ᵣ RVal_Bits (machine_x15 : bv 64%N) ∗ "x16" ↦ᵣ RVal_Bits (machine_x16 : bv 64%N) ∗ "x2" ↦ᵣ RVal_Bits ((bv_add ((Z_to_bv 64%N (decodeItemStackPointer args))) (BV 64%N 18446744073709551600%Z)) : bv 64%N) ∗ "x1" ↦ᵣ RVal_Bits (((Z_to_bv 64%N (decodeItemReturnAddress args))) : bv 64%N) ∗ "x8" ↦ᵣ RVal_Bits ((bv_add (bv_add ((Z_to_bv 64%N (decodeItemStackPointer args))) (BV 64%N 18446744073709551600%Z)) (BV 64%N 16%Z)) : bv 64%N) ∗ decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗ decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗ ((decodeItemStackPointer args - decodeItemStackBytes)) ↦ₘ{DfracOwn 1}∗ ((bv_to_little_endian (Z.of_nat 8%nat) 8%N (bv_unsigned (decodeItemSavedFramePointer args))) ++ (bv_to_little_endian (Z.of_nat 8%nat) 8%N (bv_unsigned ((Z_to_bv 64%N (decodeItemReturnAddress args))))))) ∗ ⌜(decodeItemDomainAt returnAddress decodeItemC1BDomain args) /\ (machine_x11 = (bv_add ((Z_to_bv 64%N (decodeItemInputPointer args))) (bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64%N (List.nth 0%nat (decodeItemInputBytes args) (BV 8%N 0%Z))) (BV 64%N 255%Z)) (BV 64%N 73%Z)) (BV 64%N 255%Z)) (BV 64%N 1%Z)))) /\ (bv_unsigned machine_x15 = (decodeItemInputPointer args + 1 + i)%Z) /\ ((0 <= i)%Z) /\ (bv_unsigned machine_x15 = bv_unsigned machine_x11) /\ (bv_unsigned machine_x13 = ZesuSsz.Automation2.ByteWindowFold.zesu_byte_window_fold ((decodeItemInputBytes args)) 1%nat (Z.to_nat i)) /\ (((bool_decide ((bv_signed (BV 128%N 183%Z) < bv_signed (bv_zero_extend 128%N (bv_and (bv_sign_extend 64%N (List.nth 0%nat (decodeItemInputBytes args) (BV 8%N 0%Z))) (BV 64%N 255%Z))))%Z))) = true) /\ (((negb (bool_decide ((bv_signed (bv_zero_extend 128%N (bv_and (bv_sign_extend 64%N (List.nth 0%nat (decodeItemInputBytes args) (BV 8%N 0%Z))) (BV 64%N 255%Z))) >= bv_signed (BV 128%N 192%Z))%Z)))) = true) /\ (((negb (bool_decide ((bv_signed (bv_zero_extend 128%N (bv_and (bv_add (bv_and (bv_sign_extend 64%N (List.nth 0%nat (decodeItemInputBytes args) (BV 8%N 0%Z))) (BV 64%N 255%Z)) (BV 64%N 73%Z)) (BV 64%N 255%Z))) >= bv_signed (bv_zero_extend 128%N ((Z_to_bv 64%N (decodeItemInputLength args)))))%Z)))) = true)⌝)%I := @PreOrder_Reflexive _ _ bi.entails_po _.

#[export] Instance fp_machineAt6a38_unfold : LithiumUnfold (@fp_machineAt6a38) := I.
#[export] Typeclasses Opaque fp_machineAt6a38.
#[export] Instance fp_machineAt6a38_intro `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt6a38 (args) (returnAddress) (K))
  (fp_machineAt6a38_LoopExit (args) (returnAddress) ∗ K)%I := @PreOrder_Reflexive _ _ bi.entails_po _.

