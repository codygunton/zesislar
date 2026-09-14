Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSomeHandoff.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Local Remove Hints
  IslaTraces.write_success_blocks.Index.find_body_a15168_inst
  : typeclass_instances.

Ltac write_success_optional_some_15168_trace_to_nil :=
  lazymatch goal with
  | |- context[WPasm ?trace] =>
      let trace' := (eval cbv [TRACE_LET] in trace) in
      lazymatch trace' with
      | tnil => idtac
      | _ => liAStep; write_success_optional_some_15168_trace_to_nil
      end
  | |- context[WPasm] => liAStep; write_success_optional_some_15168_trace_to_nil
  | _ => first [liAStep; write_success_optional_some_15168_trace_to_nil | shelve]
  end.

Lemma write_success_optional_some_15168_offset (sp : bv 64) :
  (bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z ->
  bv_unsigned (sp + BV 64 1744)%bv = bv_unsigned sp + 1744.
Proof.
  intro Hupper. apply bv_unsigned_add_no_wrap_64.
  rewrite bv_unsigned_BV.
  pose proof (bv_unsigned_in_range 64 sp) as Hrange.
  unfold bv_modulus in Hrange. cbn in Hrange. lia.
Qed.

Lemma write_success_optional_some_15168_alignment (sp : bv 64) :
  bv_unsigned sp `mod` 16 = 0 ->
  (bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z ->
  bv_extract 0 3 (sp + BV 64 1744)%bv = BV 3 0.
Proof.
  intros Halign Hupper. apply bv_eq.
  rewrite bv_extract_0_unsigned.
  rewrite (write_success_optional_some_15168_offset sp Hupper).
  rewrite !bv_unsigned_BV. unfold bv_wrap, bv_modulus. cbn.
  rewrite Z.add_mod; try lia.
Qed.

Lemma write_success_optional_some_15168_ram_limit :
  bv_unsigned
      (BV 64 (mapRamBase defaultMap) + BV 64 (mapRamSize defaultMap) - BV 64 8)%bv = (machineRamEnd defaultMap - 8).
Proof. vm_compute; reflexivity. Qed.

Lemma write_success_transactions_optional_address_some_15168
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1516c
    (writeSuccessTransactionsOptionalAddressSomeAt1516cSpec P) -∗
  instr_body 0x15168
    (writeSuccessTransactionsOptionalAddressSomeAt15168Spec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try liARun.
  all: iIntros "HdataOwn".
  all: iIntros "HtransactionTail".
  all: iIntros "HremainingTail".
  all: iDestruct "HtransactionTail" as "(HaccessOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(HaccessEntriesOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(HblobOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(HauthOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(%Hvalid & _)".
  all: iDestruct "HremainingTail" as "(Hremaining & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Hmmio & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Htrace & HremainingTail)".
  all: iDestruct "HremainingTail" as "(HP & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Hinv & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Hloop & _)".
  iRename select ((bv_unsigned sp + 1744) ↦ₘ _)%I into "Hbyte1744".
  iRename select ((bv_unsigned sp + 1745) ↦ₘ? 151)%I into "Htail1745".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 8 with "Hbyte1744")
    as "Huninit1744".
  iAssert ((bv_unsigned sp + 1744) ↦ₘ? 152)%I
    with "[Huninit1744 Htail1745]" as "Hscratch1744".
  { iApply (mem_mapsto_uninit_combine 1 with "Huninit1744").
    - lia.
    - have -> : bv_unsigned sp + 1744 + 1 = bv_unsigned sp + 1745 by lia.
      iExact "Htail1745". }
  iDestruct "Hinv" as "#Hinv".
  iPoseProof "Hinv" as "#HinvCopy".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant)
    in "HinvCopy".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[HspAlign HinvCopy]".
  iDestruct "HinvCopy" as "[HspLower HinvCopy]".
  iDestruct "HinvCopy" as "[HspUpper HinvCopy]".
  iDestruct "HspAlign" as "%HspAlign".
  iDestruct "HspLower" as "%HspLower".
  iDestruct "HspUpper" as "%HspUpper".
  iRename select (reg_col zesu_ram_sys_regs)%I into "Hsys".
  iDestruct "Hsys" as
    "(Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
      Hclintbase & Hclintsize & Hhtif & Hprivilege & Hmisa & Hmtvec &
      Hmstatus & Hsatp & _)".
  iAssert (reg_col zesu_ram_sys_regs)%I with
    "[Hpmp Hmisaligned Hrambase Hramsize Hrombase Hromsize Hclintbase Hclintsize
      Hhtif Hprivilege Hmisa Hmtvec Hmstatus Hsatp]" as "Hsys".
  { rewrite !reg_col_cons reg_col_nil. iFrame. }
  all: iIntros "HPC".
  all: write_success_optional_some_15168_trace_to_nil.
  Unshelve. all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; rewrite bv_unsigned_BV;
    assumption).
  all: try (apply write_success_optional_some_15168_alignment; assumption).
  all: try (rewrite (write_success_optional_some_15168_offset sp HspUpper);
    rewrite write_success_optional_some_15168_ram_limit; lia).
  all: try (rewrite (write_success_optional_some_15168_offset sp HspUpper); lia).
  all: rewrite (write_success_optional_some_15168_offset sp HspUpper).
  all: rewrite bv_unsigned_BV.
  all: lia.
  Unshelve. all: liARun.
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
  iRename select (base ↦ₘ∗ prefix)%I into "Hprefix".
  iRename select ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix)%I
    into "Hsuffix".
  iRename select (WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn processed)%I
    into "Hprocessed".
  subst LET0.
  iRename select (bv_unsigned (sp + BV 64 1744) ↦ₘ _)%I into "Hstack1744".
  iRename select ((bv_unsigned (sp + BV 64 1744) + 8) ↦ₘ? _)%I
    into "Hstack1752".
  iAssert ((bv_unsigned sp + 1744) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 265)%I
    with "[Hstack1744]" as "Hstack1744".
  { rewrite <- (write_success_optional_some_15168_offset sp HspUpper).
    iExact "Hstack1744". }
  iAssert ((bv_unsigned sp + 1752) ↦ₘ? 144)%I
    with "[Hstack1752]" as "Hstack1752".
  { replace (bv_unsigned sp + 1752) with (bv_unsigned (sp + BV 64 1744) + 8)
      by (rewrite (write_success_optional_some_15168_offset sp HspUpper); lia).
    replace 144 with
      (bv_unsigned sp + 1744 + 152 - (bv_unsigned (sp + BV 64 1744) + 8))
      by (rewrite (write_success_optional_some_15168_offset sp HspUpper); lia).
    iExact "Hstack1752". }
  all: iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  all: iSplit; [iPureIntro; exact H0|].
  iAssert (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff
    WriteSuccessTransactionsSpec.TransactionTo
    (writeSuccessTransactionsMachine1516c sp base transactions processed transaction)
    sp base transaction transactions processed remaining bytes prefix suffix tail P)%I
    with "[HsysPost Hother Hx1 Hx2 Hx5 Hx8 Hx9 Hx10 Hx11 Hx12 Hx18 Hx19 Hx20 Hx21
      Hx22 Hx23 Hx24 Hx25 Hx26 Hx27 Hstack0 Hstack104 Hstack112 Hstack120 Hstack128
      Hstack136 Hstack144 Hstack152 Hstack160 Hstack168 Hstack176 Hstack184 Hstack192
      Hstack200 Hstack208 Hstack216 Hstack224 Hstack232 Hstack240 Hstack248 Hstack256
      Hstack264 Hstack272 Hstack280 Hstack1640 Hstack1648 Hstack1656 Hstack1660 Hstack1664
      Hstack1672 Hstack1680 Hstack1744 Hstack1752 Hprefix Hsuffix Hprocessed HdataOwn
      HaccessOwn HaccessEntriesOwn HblobOwn HauthOwn Hremaining Hmmio Htrace HP Hinv Hloop]"
    as "Htarget".
  { unfold WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff,
      writeSuccessTransactionsMachine1516c,
      writeSuccessTransactionsScratch1516c.
    iFrame "HsysPost Hother Hx1 Hx2 Hx5 Hx8 Hx9 Hx10 Hx11 Hx12 Hx18 Hx19 Hx20 Hx21
      Hx22 Hx23 Hx24 Hx25 Hx26 Hx27 Hstack0 Hstack104 Hstack112 Hstack120 Hstack128
      Hstack136 Hstack144 Hstack152 Hstack160 Hstack168 Hstack176 Hstack184 Hstack192
      Hstack200 Hstack208 Hstack216 Hstack224 Hstack232 Hstack240 Hstack248 Hstack256
      Hstack264 Hstack272 Hstack280 Hstack1640 Hstack1648 Hstack1656 Hstack1660 Hstack1664
      Hstack1672 Hstack1680 Hstack1744 Hstack1752 Hprefix Hsuffix Hprocessed HdataOwn
      HaccessOwn HaccessEntriesOwn HblobOwn HauthOwn Hremaining Hmmio Htrace HP Hinv Hloop".
    iSplit.
    - iPureIntro. exact Hvalid.
    - done. }
  iExact "Htarget".
Qed.
