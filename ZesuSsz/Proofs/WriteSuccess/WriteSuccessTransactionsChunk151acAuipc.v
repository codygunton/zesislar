Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151b4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151acReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151acEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151acSetup.

Import ListNotations WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_151b4_ret_bit0 :
  bv_extract 0 1 (BV 64 0x151b4) = BV 1 0.
Proof. bv_solve. Qed.

Lemma write_success_transactions_151b4_ret_bit1 :
  bv_extract 1 1 (BV 64 0x151b4) = BV 1 0.
Proof. bv_solve. Qed.

Lemma write_success_transactions_151b4_ret_bits2 :
  bv_extract 0 2 (BV 64 0x151b4) = BV 2 0.
Proof. bv_solve. Qed.

Lemma write_success_transactions_151ac_call_bounds (sp : bv 64) :
  (mapRamBase defaultMap) <= bv_unsigned sp - 48 ->
  bv_unsigned sp + 1896 < (machineRamEnd defaultMap) ->
  (mapRamBase defaultMap) <= bv_unsigned sp - 48 /\ bv_unsigned sp < (machineRamEnd defaultMap).
Proof. lia. Qed.

Lemma write_success_transactions_15cb0_target_bits2 :
  bv_extract 0 2
    (Z_to_bv 64 86460 + 4096 + 18446744073709550256)%bv = BV 2 0.
Proof. bv_solve. Qed.

Ltac write_success_until_tnil :=
  lazymatch goal with
  | |- context[WPasm ?trace] =>
      let trace' := (eval cbv [TRACE_LET] in trace) in
      lazymatch trace' with
      | tnil => try done
      | _ => liAStep; write_success_until_tnil
      end
  | |- context[WPasm] => liAStep; write_success_until_tnil
  | _ => first [liAStep; write_success_until_tnil | shelve]
  end.

Ltac write_success_prepare_a151ac :=
  lazymatch goal with
  | Hshape2 : valu_has_shape (RegVal_Base ?v2') _ |- _ =>
      let Hmask_shape2 := fresh "Hmask_shape2" in
      let b2 := fresh "b2" in
      let Hv2 := fresh "Hv2" in
      let Hmask2 := fresh "Hmask2" in
      pose proof (valu_has_mask_shape (RegVal_Base v2') 64 0x20000 0 Hshape2)
        as Hmask_shape2;
      destruct Hmask_shape2 as [b2 [Hv2 Hmask2]];
      inversion Hv2; subst v2';
      iExists (Val_Bits (BV 64 0), tt)ₗ
  end.

Ltac write_success_solve_mask_eq :=
  iPureIntro;
  lazy [option_bind option_fmap option_map fmap mret option_ret
    guard_or mthrow option_mfail foldl bvn_to_bv decide decide_rel
    BinNat.N.eq_dec N.eq_dec N_rec N_rect bvn_n sumbool_rec sumbool_rect
    BinPos.Pos.eq_dec Pos.eq_dec positive_rect positive_rec eq_rect eq_ind_r
    eq_ind eq_sym bvn_val N.add N.sub Pos.add Pos.succ Pos.sub_mask
    Pos.double_mask Pos.succ_double_mask Pos.pred_double Pos.double_pred_mask];
  destruct (N.eq_dec 64%N 64%N) as [Hn2 | Hn2];
  [ cbn; f_equal; f_equal; cbn; simplify_eq;
    apply (proj2 (bvn_eq _ _)); split; [reflexivity|];
    cbn; unfold bvn_unsigned; cbn;
    rewrite bv_and_unsigned !bv_unsigned_BV;
    lazymatch goal with
    | Hmask : Z.land (bv_unsigned ?value) 131072 = 0
        |- Z.land (bv_unsigned ?value) 131072 = 0 => exact Hmask
    end
  | exfalso; apply Hn2; reflexivity ].

Lemma write_success_transactions_chunk_151ac_auipc
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x151b0 (writeSuccessTransactions151b0SetupSpec P) -∗
  instr_body 0x151ac (writeSuccessTransactions151acSetupSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hafter".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  iIntros "Hto _ _ Hstate HPC".
  iDestruct "Hstate" as "(Hmmio & Htrace & Houter & Hnext & _)".
  lazymatch goal with
  | H : bv_unsigned sp `mod` 16 = 0 |- _ => rename H into Halign
  end.
  zesu_name_machine_bound
    ((mapRamBase defaultMap) <= bv_unsigned sp - 48) Hmin.
  zesu_name_machine_bound
    (bv_unsigned sp + 1896 < (machineRamEnd defaultMap)) Hmax.
  unfold TRACE_LET.
  do 8 liAStep.
  unfold li_tactic, regcol_compute_hint.
  iExists (false, MaskShape 64 0x20000 0).
  iSplit; [iPureIntro; vm_compute; reflexivity|].
  cbn.
  iIntros (v2) "%Hshape2".
  destruct v2 as [v2' | | | | | | | |].
  - iIntros "Hsys2".
    write_success_until_tnil.
  - done.
  - done.
  - done.
  - done.
  - done.
  - done.
  - done.
  - done.
  Unshelve.
  all: write_success_prepare_a151ac.
  Unshelve.
  all: iSplit.
  Unshelve.
  all: try write_success_solve_mask_eq.
  all: liARun.
  all: iRename select
    (((∃ vact : valu,
        ⌜valu_has_shape vact (BitsShape 64)⌝ ∗ "x1" ↦ᵣ vact) ∗ _)%I)
    into "HotherExpanded".
  all: iDestruct "HotherExpanded" as "(Hx1 & HotherRest)".
  all: iDestruct "Hx1" as (v1) "(%Hshape1 & Hx1)".
  all: iDestruct "HotherRest" as
    "(H3 & H4 & H6 & H7 & H12 & H13 & H14 & H15 & H16 & H17 &
      H28 & H29 & H30 & H31 & _)".
  all: iDestruct "H12" as (v12) "(%Hshape12 & H12)".
  all: iDestruct "H13" as (v13) "(%Hshape13 & H13)".
  all: iDestruct "H14" as (v14) "(%Hshape14 & H14)".
  all: iDestruct "H15" as (v15) "(%Hshape15 & H15)".
  all: iDestruct "H16" as (v16) "(%Hshape16 & H16)".
  all: iDestruct "H17" as (v17) "(%Hshape17 & H17)".
  all: destruct (valu_has_bits_shape v12 64 Hshape12) as (b12 & ->).
  all: destruct (valu_has_bits_shape v13 64 Hshape13) as (b13 & ->).
  all: destruct (valu_has_bits_shape v14 64 Hshape14) as (b14 & ->).
  all: destruct (valu_has_bits_shape v15 64 Hshape15) as (b15 & ->).
  all: destruct (valu_has_bits_shape v16 64 Hshape16) as (b16 & ->).
  all: destruct (valu_has_bits_shape v17 64 Hshape17) as (b17 & ->).
  all: liARun.
  all: iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  all: repeat iSplit; try iPureIntro; try assumption.
  all: rewrite /writeSuccessTransactionsMachine151b0 /reg_col.
  all: cbn. all: iFrame.
  all: repeat iSplit; try (iPureIntro; cbn; done).
  all: zesu_run.
Qed.
(**
  all: iRename select ("x1" ↦ᵣ RVal_Bits _)%I into "Hx1Current".
  all: iExists (Z_to_bv 64 90540, tt)ₗ.
  all: cbn.
  all: replace (Z_to_bv 64 90540)
    with (Z_to_bv 64 86444 + 4096)%bv by bv_solve.
  all: iFrame "Hsys2 Hx1Current".
  all: iSplit; first (iPureIntro; bv_solve).
  all: have Htarget :
      bv_unsigned
        (bv_or
          (bv_and
            ((Z_to_bv 64 86444 + 4096) + 18446744073709550340)
            18446744073709551614)
          0) = 0x15cb0 by native_compute.
  all: rewrite Htarget.
  all: iSpecialize ("Hu256Hidden" with "[]"); first done.
  all: iApply (instr_pre_wand 0x15cb0 0x15cb0 true true
    with "Hu256Hidden"); [done | reflexivity |].
  all: iIntros "Hentry".
  all: iDestruct "Hentry" as "(Hsys & H1 & _)".
  all: iAssert (reg_col zesu_ram_sys_regs)%I with "[Hsys]" as "HsysCol".
  { rewrite /reg_col. iExact "Hsys". }
  all: iEval (replace (Z_to_bv 64 (86448 + 4)) with (BV 64 86452)
    by bv_solve) in "H1".
  all: iRename select ("x2" ↦ᵣ RVal_Bits sp)%I into "H2Call".
  all: iRename select ("x5" ↦ᵣ _)%I into "H5Call".
  all: iRename select ("x8" ↦ᵣ _)%I into "H8Call".
  all: iRename select ("x9" ↦ᵣ _)%I into "H9Call".
  all: iRename select ("x10" ↦ᵣ _)%I into "H10Call".
  all: iRename select ("x11" ↦ᵣ _)%I into "H11Call".
  all: iRename select ("x18" ↦ᵣ _)%I into "H18Call".
  all: iRename select ("x19" ↦ᵣ _)%I into "H19Call".
  all: iRename select ("x20" ↦ᵣ _)%I into "H20Call".
  all: iRename select ("x21" ↦ᵣ _)%I into "H21Call".
  all: iRename select ("x22" ↦ᵣ _)%I into "H22Call".
  all: iRename select ("x23" ↦ᵣ _)%I into "H23Call".
  all: iRename select ("x24" ↦ᵣ _)%I into "H24Call".
  all: iRename select ("x25" ↦ᵣ _)%I into "H25Call".
  all: iRename select ("x26" ↦ᵣ _)%I into "H26Call".
  all: iRename select ("x27" ↦ᵣ _)%I into "H27Call".
  all: pose proof write_success_transactions_151b4_ret_bit0 as HretBit0.
  all: pose proof write_success_transactions_151b4_ret_bit1 as HretBit1.
  all: pose proof write_success_transactions_151b4_ret_bits2 as HretBits2.
  all: have HcallBounds :
      (mapRamBase defaultMap) <= bv_unsigned sp - 48 /\ bv_unsigned sp < (machineRamEnd defaultMap)
    by exact (write_success_transactions_151ac_call_bounds sp Hmin Hmax).
  all: iAssert (((bv_unsigned sp - 48) ↦ₘ? 48 -∗
      writeSuccessTransactionsScratch1519c
        sp base transactions processed transaction))%I
    with "[-HnextHeld Houter HsysCol H1 H2Call H5Call H6 H7 H8Call H9Call H10Call
      H11Call H12 H13 H14 H15 H16 H17 H18Call H19Call H20Call H21Call
      H22Call H23Call H24Call H25Call H26Call H27Call H28 H29 H30 H31
      HcallScratch H3 H4 Hmmio Htrace]" as "HscratchFrame".
  { iIntros "HscratchLower".
    iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
      with "[HscratchLower HscratchRest]" as "HscratchAll".
    { iApply (mem_mapsto_uninit_combine 48 with "HscratchLower"); first lia.
      iExact "HscratchRest". }
    rewrite /writeSuccessTransactionsScratch1519c.
    iFrame. }
  all: iAssert (reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      ["x3"; "x4"]))%I with "[H3 H4]" as "H34".
  { rewrite /reg_col. cbn. iFrame. }
  all: iPoseProof (write_success_transactions_151ac_return_frame_intro P sp
    base transaction transactions processed remaining bytes prefix suffix tail
    with "Houter H34 HscratchFrame") as "Hframe".
  all: iSpecialize ("HnextHeld" with "[]"); first done.
  all: iAssert (instr_pre 0x151b4
      (writeSuccessTransactions151acCallRet sp transaction remaining tail))%I
    with "[HnextHeld Hframe]" as "Hreturn".
  { iApply (instr_pre_wand 0x151b4 0x151b4 false true with "HnextHeld");
      [done | reflexivity |].
    iIntros "Hpost".
    iApply (write_success_transactions_151ac_return_adapter P sp base
      transaction transactions processed remaining bytes prefix suffix tail with
      "Hpost Hframe"). }
  all: iAssert (reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      ["x6"; "x7"; "x28"; "x29"; "x30"; "x31"]))%I
    with "[H6 H7 H28 H29 H30 H31]" as "HtmpCall".
  { rewrite /reg_col. cbn. iFrame. }
  all: iPoseProof (write_success_transactions_151ac_call_entry_intro
    sp b b12 b13 b14 b15 b16 b17 transaction remaining tail Halign HcallBounds
    with "HsysCol H5Call HtmpCall H10Call H11Call H12 H13 H14 H15 H16 H17
      H8Call H9Call H18Call H19Call H20Call H21Call H22Call H23Call H24Call
      H25Call H26Call H27Call H1 H2Call HcallScratch Hmmio Htrace Hreturn")
    as "HcallEntry".
  all: iApply (write_success_transactions_151ac_call_entry sp b b12 b13 b14
    b15 b16 b17 transaction remaining tail with "HcallEntry").
Qed.
*)

(**
Lemma write_success_transactions_chunk_151ac
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  instr_body 0x151b4 (writeSuccessTransactionsAt151b4Spec P) -∗
  instr_body 0x151ac (writeSuccessTransactionsAt151acSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hu256 Hnext".
  iPoseProof (write_success_transactions_chunk_151ac_core P with
    "Hlookup Hcode Hu256") as "Hcore".
  iEval (rewrite instr_pre'_eq) in "Hcore".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iApply "Hcore".
  iApply (write_success_transactions_151ac_setup P with "Hnext Hentry").
Qed.
*)
