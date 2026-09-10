From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15190Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1517cBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_optional_address_some_15190
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1519c (writeSuccessTransactionsAt1519cSpec P) -∗
  instr_body 0x15190 (writeSuccessTransactionsOptionalAddressSomeAt15190Spec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond; try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve; try lia; try iFrame.
  Unshelve.
  iRename select (reg_col zesu_ram_sys_regs)%I into "Hsys".
  iRename select (reg_col
    [(KindReg "x1", BitsShape 64); (KindReg "x12", BitsShape 64);
     (KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64);
     (KindReg "x15", BitsShape 64); (KindReg "x16", BitsShape 64);
     (KindReg "x17", BitsShape 64); (KindReg "x5", BitsShape 64);
     (KindReg "x6", BitsShape 64); (KindReg "x7", BitsShape 64);
     (KindReg "x28", BitsShape 64); (KindReg "x29", BitsShape 64);
     (KindReg "x30", BitsShape 64); (KindReg "x31", BitsShape 64)])%I
    into "Hcaller".
  iRename select (reg_col
    [(KindReg "x8", ExactShape _); (KindReg "x9", ExactShape _);
     (KindReg "x18", ExactShape _); (KindReg "x19", ExactShape _);
     (KindReg "x20", ExactShape _); (KindReg "x21", ExactShape _);
     (KindReg "x22", ExactShape _); (KindReg "x23", ExactShape _);
     (KindReg "x24", ExactShape _); (KindReg "x25", ExactShape _);
     (KindReg "x26", ExactShape _); (KindReg "x27", ExactShape _)])%I
    into "Hsaved".
  iRename select (reg_col
    [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)])%I
    into "H34".
  iRename select ("x10" ↦ᵣ _)%I into "H10".
  iRename select ("x11" ↦ᵣ _)%I into "H11".
  iRename select ("x2" ↦ᵣ _)%I into "H2".
  iRename select (writeSuccessTransactionsOptionalAddressSomeFrame P _ _ _ _ _ _ _ _ _ _)
    into "Hframe".
  iRename select (mmio_range 0x2401a0c0 16)%I into "Hmmio".
  iRename select (spec_trace _)%I into "Htrace".
  iEval (unfold writeSuccessTransactionsOptionalAddressSomeFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining & HP & Hinv &
      Hexit & %Hto & _)".
  iRename select ((bv_unsigned sp - 48) ↦ₘ? 152)%I into "Hstack0".
  iRename select ((bv_unsigned sp + 104) ↦ₘ _)%I into "Hstack104".
  iRename select ((bv_unsigned sp + 112) ↦ₘ _)%I into "Hstack112".
  iRename select ((bv_unsigned sp + 120) ↦ₘ _)%I into "Hstack120".
  iRename select ((bv_unsigned sp + 128) ↦ₘ _)%I into "Hstack128".
  iRename select ((bv_unsigned sp + 136) ↦ₘ _)%I into "Hstack136".
  iRename select ((bv_unsigned sp + 144) ↦ₘ _)%I into "Hstack144".
  iRename select ((bv_unsigned sp + 152) ↦ₘ _)%I into "Hstack152".
  iRename select ((bv_unsigned sp + 160) ↦ₘ _)%I into "Hstack160".
  iRename select ((bv_unsigned sp + 168) ↦ₘ _)%I into "Hstack168".
  iRename select ((bv_unsigned sp + 176) ↦ₘ _)%I into "Hstack176".
  iRename select ((bv_unsigned sp + 184) ↦ₘ _)%I into "Hstack184".
  iRename select ((bv_unsigned sp + 192) ↦ₘ _)%I into "Hstack192".
  iRename select ((bv_unsigned sp + 200) ↦ₘ _)%I into "Hstack200".
  iRename select ((bv_unsigned sp + 208) ↦ₘ _)%I into "Hstack208".
  iRename select ((bv_unsigned sp + 216) ↦ₘ _)%I into "Hstack216".
  iRename select ((bv_unsigned sp + 224) ↦ₘ _)%I into "Hstack224".
  iRename select ((bv_unsigned sp + 232) ↦ₘ _)%I into "Hstack232".
  iRename select ((bv_unsigned sp + 240) ↦ₘ _)%I into "Hstack240".
  iRename select ((bv_unsigned sp + 248) ↦ₘ _)%I into "Hstack248".
  iRename select ((bv_unsigned sp + 256) ↦ₘ _)%I into "Hstack256".
  iRename select ((bv_unsigned sp + 264) ↦ₘ _)%I into "Hstack264".
  iRename select ((bv_unsigned sp + 272) ↦ₘ _)%I into "Hstack272".
  iRename select ((bv_unsigned sp + 280) ↦ₘ? 1360)%I into "Hstack280".
  iRename select ((bv_unsigned sp + 1640) ↦ₘ _)%I into "Hstack1640".
  iRename select ((bv_unsigned sp + 1648) ↦ₘ _)%I into "Hstack1648".
  iRename select ((bv_unsigned sp + 1656) ↦ₘ _)%I into "Hstack1656".
  iRename select ((bv_unsigned sp + 1660) ↦ₘ? 4)%I into "Hstack1660".
  iRename select ((bv_unsigned sp + 1664) ↦ₘ _)%I into "Hstack1664".
  iRename select ((bv_unsigned sp + 1672) ↦ₘ _)%I into "Hstack1672".
  iRename select ((bv_unsigned sp + 1680) ↦ₘ? 64)%I into "Hstack1680".
  iRename select ((bv_unsigned sp + 1744) ↦ₘ _)%I into "Hstack1744".
  iRename select ((bv_unsigned sp + 1752) ↦ₘ _)%I into "Hstack1752".
  iRename select ((bv_unsigned sp + 1760) ↦ₘ _)%I into "Hstack1760".
  iRename select ((bv_unsigned sp + 1764) ↦ₘ? 132)%I into "Htail1764".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hcaller Hsaved H34".
  iDestruct "Hcaller" as
    "(H1 & H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 & H29 &
      H30 & H31 & _)".
  iDestruct "H5" as (v5) "(%Hv5 & H5)".
  iAssert ("x5" ↦ᵣ: fun value =>
      ⌜valu_has_shape value (BitsShape 64)⌝)%I with "[H5]" as "H5Target".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists v5. iFrame "H5". iPureIntro. exact Hv5. }
  iDestruct "H34" as "(H3 & H4 & _)".
  iDestruct "Hsaved" as
    "(H8Raw & H9Raw & H18Raw & H19Raw & H20Raw & H21Raw & H22Raw & H23Raw &
      H24Raw & H25Raw & H26Raw & H27Raw & _)".
  iDestruct "H8Raw" as (v8) "(%Hv8 & H8)".
  iDestruct "H9Raw" as (v9) "(%Hv9 & H9)".
  iDestruct "H18Raw" as (v18) "(%Hv18 & H18)".
  iDestruct "H19Raw" as (v19) "(%Hv19 & H19)".
  iDestruct "H20Raw" as (v20) "(%Hv20 & H20)".
  iDestruct "H21Raw" as (v21) "(%Hv21 & H21)".
  iDestruct "H22Raw" as (v22) "(%Hv22 & H22)".
  iDestruct "H23Raw" as (v23) "(%Hv23 & H23)".
  iDestruct "H24Raw" as (v24) "(%Hv24 & H24)".
  iDestruct "H25Raw" as (v25) "(%Hv25 & H25)".
  iDestruct "H26Raw" as (v26) "(%Hv26 & H26)".
  iDestruct "H27Raw" as (v27) "(%Hv27 & H27)".
  cbn in Hv8, Hv9, Hv18, Hv19, Hv20, Hv21, Hv22, Hv23, Hv24, Hv25, Hv26, Hv27.
  subst v8; subst v9; subst v18; subst v19; subst v20; subst v21.
  subst v22; subst v23; subst v24; subst v25; subst v26; subst v27.
  iAssert ((∃ value : valu, ⌜valu_has_shape value (BitsShape 64)⌝ ∗
      KindReg "x10" ↦ᵣₖ value)%I) with "[H10]" as "H10Shape".
  { iExists (RVal_Bits b10). iSplit; [iPureIntro; cbn; done | iFrame "H10"]. }
  iAssert ((∃ value : valu, ⌜valu_has_shape value (BitsShape 64)⌝ ∗
      KindReg "x11" ↦ᵣₖ value)%I) with "[H11]" as "H11Shape".
  { iExists (RVal_Bits b11). iSplit; [iPureIntro; cbn; done | iFrame "H11"]. }
  iAssert (reg_col writeSuccessTransactions1519cOtherRegShapes)%I
    with "[H1 H3 H4 H6 H7 H10Shape H11Shape H12 H13 H14 H15 H16 H17
      H28 H29 H30 H31]" as "Hother".
  { rewrite /writeSuccessTransactions1519cOtherRegShapes
      /writeSuccessTransactions1519cOtherRegisters /= !reg_col_cons reg_col_nil.
    iSplitL "H1"; [iExact "H1"|].
    iSplitL "H3"; [iExact "H3"|].
    iSplitL "H4"; [iExact "H4"|].
    iSplitL "H6"; [iExact "H6"|].
    iSplitL "H7"; [iExact "H7"|].
    iSplitL "H10Shape"; [iExact "H10Shape"|].
    iSplitL "H11Shape"; [iExact "H11Shape"|].
    iSplitL "H12"; [iExact "H12"|].
    iSplitL "H13"; [iExact "H13"|].
    iSplitL "H14"; [iExact "H14"|].
    iSplitL "H15"; [iExact "H15"|].
    iSplitL "H16"; [iExact "H16"|].
    iSplitL "H17"; [iExact "H17"|].
    iSplitL "H28"; [iExact "H28"|].
    iSplitL "H29"; [iExact "H29"|].
    iSplitL "H30"; [iExact "H30"|].
    iSplitL "H31"; [iExact "H31"|].
    done. }
  iAssert (writeSuccessTransactionsMachine1519c
      sp base transactions processed transaction)%I
    with "[Hsys Hother H2 H5Target H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27
      Hstack0 Hstack104 Hstack112 Hstack120 Hstack128 Hstack136 Hstack144
      Hstack152 Hstack160 Hstack168 Hstack176 Hstack184 Hstack192 Hstack200
      Hstack208 Hstack216 Hstack224 Hstack232 Hstack240 Hstack248 Hstack256
      Hstack264 Hstack272 Hstack280 Hstack1640 Hstack1648 Hstack1656 Hstack1660
      Hstack1664 Hstack1672 Hstack1680 Hstack1744 Hstack1752 Hstack1760 Htail1764]"
    as "Hmachine".
  { rewrite /writeSuccessTransactionsMachine1519c
      /writeSuccessTransactionsScratch1519c.
    destruct (writeSuccessTransactionTo transaction) as [address|] eqn:HtoValue.
    2: { exfalso. apply Hto. reflexivity. }
    iSplitL "Hsys"; [iExact "Hsys"|].
    iSplitL "Hother"; [iExact "Hother"|].
    iSplitL "H2"; [iExact "H2"|].
    iSplitL "H5Target"; [iExact "H5Target"|].
    iFrame "H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27
      Hstack0 Hstack104 Hstack112 Hstack120 Hstack128 Hstack136 Hstack144
      Hstack152 Hstack160 Hstack168 Hstack176 Hstack184 Hstack192 Hstack200
      Hstack208 Hstack216 Hstack224 Hstack232 Hstack240 Hstack248 Hstack256
      Hstack264 Hstack272 Hstack280 Hstack1640 Hstack1648 Hstack1656 Hstack1660
      Hstack1664 Hstack1672 Hstack1680 Hstack1744 Hstack1752 Hstack1760 Htail1764". }
  iExists (tail, suffix, prefix, bytes, remaining, processed, transactions,
    transaction, base, sp, tt)ₗ.
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff).
  iFrame "Hmachine Hprefix Hsuffix Hprocessed Htransaction Hremaining Hmmio Htrace HP
    Hinv Hexit".
Qed.
