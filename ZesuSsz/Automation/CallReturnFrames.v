Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessEpilogueBlock WriteSuccessNativeContract WriteSuccessPrologueSpec.
Import ListNotations.
Lemma zesu_mask_return_even (ra : bv 64) :
 bv_extract 0 2 ra = BV 2 0 ->
 bv_unsigned (bv_or (bv_and (ra + 0)%bv (BV 64 18446744073709551614)) (BV 64 0)) = bv_unsigned ra.
Proof.
 intro Hret. bv_simplify_arith Hret.
 rewrite bv_or_unsigned bv_and_unsigned bv_add_0_r; last done.
 change (Z.lor (Z.land (bv_unsigned ra) 18446744073709551614) 0 = bv_unsigned ra).
 rewrite Z.lor_0_r.
 have Heven : bv_unsigned ra = Z.shiftl (Z.shiftr (bv_unsigned ra) 1) 1.
 { rewrite (Z.shiftl_mul_pow2 (Z.shiftr (bv_unsigned ra) 1) 1); [|lia].
   rewrite (Z.shiftr_div_pow2 (bv_unsigned ra) 1); [|lia]. cbn. bv_solve. }
 replace 18446744073709551614 with (Z.shiftl (Z.ones 63) 1) by (vm_compute; reflexivity).
 rewrite {1}Heven. rewrite -Z.shiftl_land Z.land_ones; [|lia..].
 rewrite Z.mod_small.
 - rewrite -Heven. reflexivity.
 - rewrite Z.shiftr_div_pow2; [|lia..]. cbn. clear Hret Heven. bv_solve.
Qed.

Ltac zesu_predicate_chain_from_shapes names :=
  lazymatch names with
  | [] => idtac
  | ?head :: ?tail =>
      let actual := fresh "currentRegisterValue" in
      iDestruct head as (actual) "[_ HcurrentRegister]";
      iExists actual; iFrame "HcurrentRegister";
      zesu_predicate_chain_from_shapes tail
  end.

Lemma zesu_call_ret_to_epilogue `{!islaG Sigma} `{!threadG}
    (stackSize : Z) (sp callReturn savedReturn : bv 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : valu)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (R Q F : iProp Sigma) :
  bv_unsigned sp `mod` 8 = 0 ->
  mapRamBase defaultMap <= bv_unsigned sp + 1896 ->
  bv_unsigned sp + 2000 < machineRamEnd defaultMap ->
  bv_extract 0 1 savedReturn = BV 1 0 ->
  bv_extract 1 1 savedReturn = BV 1 0 ->
  bv_extract 0 2 savedReturn = BV 2 0 ->
  (F ⊣⊢ writeSuccessReturnedCallerRegisters ∗
    (bv_unsigned sp - stackSize) ↦ₘ? stackSize ∗ R ∗ Q)%I ->
  reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] -∗
  zesu_c_call_ret stackSize [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11]
    callReturn sp (fun _ => R) -∗
  writeSuccessEpilogueSavedSlots sp savedReturn s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 -∗
  Q -∗ instr_pre (bv_unsigned savedReturn)
    (writeSuccessEpiloguePost sp savedReturn s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F) -∗
  writeSuccessEpilogueSpec F.
Proof.
  intros HspAlign Hlow Hhigh Hret1 Hret2 Hret Hframe.
  iIntros "Hother Hpost Hslots HQ Hreturn".
  iEval (unfold zesu_c_call_ret) in "Hpost".
  iDestruct "Hpost" as "(Hsys & Hcols & Hsaved & Hbits)".
  iEval (rewrite /writeSuccessEpilogueSpec).
  iExists sp, savedReturn, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11.
  iFrame "Hsys".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hcols".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hsaved".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hother".
  iDestruct "Hcols" as "(H1 & H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 & H29 & H30 & H31 & _)".
  iDestruct "Hsaved" as "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & _)".
  iDestruct "Hother" as "(H3 & H4 & _)".
  iEval (rewrite /writeSuccessOtherRegShapes /writeSuccessOtherRegisters !reg_col_cons reg_col_nil).
  iFrame "H3 H4 H13 H14 H15 H16 H17 H5 H6 H7 H28 H29 H30 H31".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hbits".
  iDestruct "Hbits" as (r10) "[Hr10 Hbits]".
  iDestruct "Hbits" as (a0) "[%Heq10 Hbits]".
  iDestruct "Hbits" as (r11) "[Hr11 Hbits]".
  iDestruct "Hbits" as (a1) "[%Heq11 Hbits]".
  iDestruct "Hbits" as "(H2 & Hstack & HR)".
  subst r10 r11.
  iDestruct "H1" as (r1) "[_ Hr1]".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iExists r1. iFrame "Hr1 H2".
  zesu_predicate_chain_from_shapes ["H8";"H9";"H18";"H19";"H20";"H21";"H22";"H23";"H24";"H25";"H26";"H27"].
  have Hmask := zesu_mask_return_even savedReturn Hret. rewrite Hmask.
  iFrame "Hslots Hreturn".
  repeat iSplit; try iPureIntro; try assumption.
  rewrite Hframe /writeSuccessReturnedCallerRegisters.
  iDestruct "H12" as (r12) "[%Hshape12 Hr12]".
  apply valu_has_bits_shape in Hshape12.
  destruct Hshape12 as [a2 Heq12]. subst r12.
  iFrame "Hstack HR HQ". iExists a0, a1, a2. iFrame.
Qed.
Print Assumptions zesu_mask_return_even.
Print Assumptions zesu_call_ret_to_epilogue.
