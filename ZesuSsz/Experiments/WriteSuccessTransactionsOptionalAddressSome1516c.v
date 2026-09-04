From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome15168.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSomeHandoff.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_optional_address_some_1516c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15170 (writeSuccessTransactionsOptionalAddressSomeAt15170Spec P) -∗
  instr_body 0x1516c (writeSuccessTransactionsOptionalAddressSomeAt1516cSpec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources) in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond; try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve; try lia; try iFrame.
  Unshelve. all: try liARun.
  all: iIntros "Hdata HtransactionTail HremainingTail".
  all: iDestruct "HtransactionTail" as "(HaccessOwn & HaccessEntriesOwn & HblobOwn & HauthOwn & %Hvalid & _)".
  all: iDestruct "HremainingTail" as "(Hremaining & Hmmio & Htrace & HP & Hinv & Hloop & _)".
  iRename select ((bv_unsigned sp + 1752) ↦ₘ? 144)%I into "Htail1752".
  iDestruct (mem_mapsto_uninit_split 8 with "Htail1752") as "[Hslot1752 Htail1760]"; [lia|].
  iDestruct "Hinv" as "#Hinv".
  iPoseProof "Hinv" as "#HinvCopy".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant) in "HinvCopy".
  do 9 (iDestruct "HinvCopy" as "[_ HinvCopy]").
  iDestruct "HinvCopy" as "[HspAlign HinvCopy]".
  iDestruct "HinvCopy" as "[HspLower HinvCopy]".
  iDestruct "HinvCopy" as "[HspUpper _]".
  iDestruct "HspAlign" as "%HspAlign".
  iDestruct "HspLower" as "%HspLower".
  iDestruct "HspUpper" as "%HspUpper".
  liARun.
  Unshelve. all: prepare_sidecond; try assumption; try bv_solve; try lia.
  Unshelve.
  iRename select (reg_col zesu_ram_sys_regs)%I into "HsysPost".
  iRename select (reg_col writeSuccessTransactions15168OtherRegShapes)%I
    into "Hother".
  iRename select ("x1" ↦ᵣ _)%I into "Hx1".
  iRename select ("x2" ↦ᵣ _)%I into "Hx2".
  iRename select ("x5" ↦ᵣ _)%I into "Hx5".
  iRename select ("x8" ↦ᵣ _)%I into "Hx8".
  iRename select ("x9" ↦ᵣ _)%I into "Hx9".
  iRename select ("x10" ↦ᵣ _)%I into "Hx10".
  iRename select ("x11" ↦ᵣ _)%I into "Hx11".
  iRename select ("x12" ↦ᵣ _)%I into "Hx12".
  iRename select ("x18" ↦ᵣ _)%I into "Hx18".
  iRename select ("x19" ↦ᵣ _)%I into "Hx19".
  iRename select ("x20" ↦ᵣ _)%I into "Hx20".
  iRename select ("x21" ↦ᵣ _)%I into "Hx21".
  iRename select ("x22" ↦ᵣ _)%I into "Hx22".
  iRename select ("x23" ↦ᵣ _)%I into "Hx23".
  iRename select ("x24" ↦ᵣ _)%I into "Hx24".
  iRename select ("x25" ↦ᵣ _)%I into "Hx25".
  iRename select ("x26" ↦ᵣ _)%I into "Hx26".
  iRename select ("x27" ↦ᵣ _)%I into "Hx27".
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
  iRename select (base ↦ₘ∗ prefix)%I into "Hprefix".
  iRename select ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix)%I
    into "Hsuffix".
  iRename select
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn
      processed)%I into "Hprocessed".
  iRename select ((bv_unsigned sp + 1752 + 8) ↦ₘ? _)%I into "Htail1760".
  iAssert ((bv_unsigned sp + 1760) ↦ₘ? 136)%I
    with "[Htail1760]" as "Htail1760".
  { replace (bv_unsigned sp + 1760) with (bv_unsigned sp + 1752 + 8) by lia.
    replace 136 with (144 - 8) by lia.
    iExact "Htail1760". }
  iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  iSplit; [iPureIntro; exact H0|].
  unfold WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff,
    writeSuccessTransactionsMachine15170,
    writeSuccessTransactions1516cRegisters,
    writeSuccessTransactionsScratch1516Prefix,
    writeSuccessTransactionsScratch15170.
  iFrame "HsysPost Hother Hx1 Hx2 Hx5 Hx8 Hx9 Hx10 Hx11 Hx12 Hx18 Hx19
    Hx20 Hx21 Hx22 Hx23 Hx24 Hx25 Hx26 Hx27 Hstack0 Hstack104 Hstack112
    Hstack120 Hstack128 Hstack136 Hstack144 Hstack152 Hstack160 Hstack168
    Hstack176 Hstack184 Hstack192 Hstack200 Hstack208 Hstack216 Hstack224
    Hstack232 Hstack240 Hstack248 Hstack256 Hstack264 Hstack272 Hstack280
    Hstack1640 Hstack1648 Hstack1656 Hstack1660 Hstack1664 Hstack1672
    Hstack1680 Hstack1744 Hstack1752 Htail1760 Hprefix Hsuffix Hprocessed Hdata
    HaccessOwn HaccessEntriesOwn HblobOwn HauthOwn Hremaining Hmmio Htrace HP
    Hinv Hloop".
  iSplit; [iPureIntro; exact Hvalid | done].
Qed.
