Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151b4.

Import ListNotations.

Definition writeSuccessTransactions151acSaved
    (transaction : writeSuccessTransaction) : list valu :=
  [RVal_Bits (writeSuccessTransactionWord transaction 192);
   RVal_Bits (writeSuccessTransactionWord transaction 16);
   RVal_Bits (writeSuccessTransactionWord transaction 48);
   RVal_Bits (writeSuccessTransactionWord transaction 224);
   RVal_Bits (writeSuccessTransactionWord transaction 56);
   RVal_Bits (writeSuccessTransactionWord transaction 72);
   RVal_Bits (writeSuccessTransactionWord transaction 200);
   RVal_Bits (writeSuccessTransactionWord transaction 24);
   RVal_Bits (writeSuccessTransactionWord transaction 8);
   RVal_Bits (writeSuccessTransactionWord transaction 0);
   RVal_Bits (writeSuccessTransactionWord transaction 184);
   RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))].

Definition writeSuccessTransactions151acCallRet
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (transaction : writeSuccessTransaction)
    (remaining : list writeSuccessTransaction) (tail : spec) : iProp Sigma :=
  zesu_c_call_ret 48 (writeSuccessTransactions151acSaved transaction)
    (BV 64 0x151b4) sp
    (fun _ =>
      mmio_range (machineOutputAddress defaultMap) 16 ∗
      spec_trace
        (writeSuccessTransactionPhaseEvents TransactionData sp transaction
          (writeSuccessTransactionsEvents sp remaining tail)) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactions151acCallRet) := I.

Definition writeSuccessTransactions151acReturnFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x3"; "x4"]) ∗
   base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsProcessedOwn processed ∗
   writeSuccessTransactionOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗ P ∗
   writeSuccessTransactionsInvariant
     sp base transactions processed (transaction :: remaining)
     bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit sp base transactions bytes tail P) ∗
   ((bv_unsigned sp - 48) ↦ₘ? 48 -∗
      writeSuccessTransactionsScratch1519c
        sp base transactions processed transaction) ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactions151acReturnFrame) := I.

Lemma write_success_transactions_151ac_return_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactions151acCallRet sp transaction remaining tail -∗
  writeSuccessTransactions151acReturnFrame P sp base transaction transactions
    processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsAt151b4Spec P.
Proof.
  iStartProof. iIntros "Hpost Hframe".
  iEval (unfold writeSuccessTransactions151acReturnFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hframed & Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining &
      HP & Hinv & Hexit & HscratchFrame & _)".
  iEval (unfold writeSuccessTransactions151acCallRet,
    writeSuccessTransactions151acSaved, zesu_c_call_ret) in "Hpost".
  iDestruct "Hpost" as "(Hsys & Hcaller & Hsaved & Hrest)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hframed Hcaller Hsaved".
  iDestruct "Hframed" as "(H3 & H4 & _)".
  iDestruct "Hcaller" as
    "(H1 & H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 &
      H28 & H29 & H30 & H31 & _)".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 &
      H26 & H27 & _)".
  iDestruct "H8" as (v8) "(%Hv8 & H8)".
  iDestruct "H9" as (v9) "(%Hv9 & H9)".
  iDestruct "H18" as (v18) "(%Hv18 & H18)".
  iDestruct "H19" as (v19) "(%Hv19 & H19)".
  iDestruct "H20" as (v20) "(%Hv20 & H20)".
  iDestruct "H21" as (v21) "(%Hv21 & H21)".
  iDestruct "H22" as (v22) "(%Hv22 & H22)".
  iDestruct "H23" as (v23) "(%Hv23 & H23)".
  iDestruct "H24" as (v24) "(%Hv24 & H24)".
  iDestruct "H25" as (v25) "(%Hv25 & H25)".
  iDestruct "H26" as (v26) "(%Hv26 & H26)".
  iDestruct "H27" as (v27) "(%Hv27 & H27)".
  cbn in Hv8, Hv9, Hv18, Hv19, Hv20, Hv21, Hv22, Hv23, Hv24, Hv25,
    Hv26, Hv27.
  subst v8; subst v9; subst v18; subst v19; subst v20; subst v21.
  subst v22; subst v23; subst v24; subst v25; subst v26; subst v27.
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)". subst r10.
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11)
    "(%Hr11 & H2 & Hstack & Hmmio & Htrace & _)". subst r11.
  iPoseProof ("HscratchFrame" with "Hstack") as "Hscratch".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iEval (unfold writeSuccessTransactionsMachine151b4,
    writeSuccessTransactions151b4OtherRegShapes,
    writeSuccessTransactions151b4OtherRegisters, reg_col).
  cbn.
  iFrame.
  iSplit; iPureIntro; done.
Qed.

Definition writeSuccessTransactions151acCallEntry
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (b5 b12 b13 b14 b15 b16 b17 : bv 64)
    (transaction : writeSuccessTransaction)
    (remaining : list writeSuccessTransaction) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x5" ↦ᵣ RVal_Bits b5 ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
     ["x6"; "x7"; "x28"; "x29"; "x30"; "x31"]) ∗
   "x10" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
   "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
   "x12" ↦ᵣ RVal_Bits b12 ∗ "x13" ↦ᵣ RVal_Bits b13 ∗
   "x14" ↦ᵣ RVal_Bits b14 ∗ "x15" ↦ᵣ RVal_Bits b15 ∗
   "x16" ↦ᵣ RVal_Bits b16 ∗ "x17" ↦ᵣ RVal_Bits b17 ∗
   reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
     ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]
     (writeSuccessTransactions151acSaved transaction)) ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x151b4) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48 /\ bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (OutputEvents.writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 32)
       (writeSuccessTransactionPhaseEvents TransactionData sp transaction
         (writeSuccessTransactionsEvents sp remaining tail))) ∗
   instr_pre 0x151b4
     (writeSuccessTransactions151acCallRet sp transaction remaining tail) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactions151acCallEntry) := I.

Lemma write_success_transactions_151ac_call_entry
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (b5 b12 b13 b14 b15 b16 b17 : bv 64)
    (transaction : writeSuccessTransaction)
    (remaining : list writeSuccessTransaction) (tail : spec) :
  writeSuccessTransactions151acCallEntry sp b5 b12 b13 b14 b15 b16 b17
    transaction remaining tail -∗
  zesuEncoderU256CallSpec.
Proof.
  iStartProof. iIntros "Hentry".
  iEval (unfold writeSuccessTransactions151acCallEntry) in "Hentry".
  iDestruct "Hentry" as
    "(Hsys & H5 & Htmp & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
      Hsaved & H1 & H2 & %Halign & %Hbounds & Hstack & Hmmio & Htrace &
      Hreturn & _)".
  iEval (unfold zesuEncoderU256CallSpec, zesu_c_call).
  iExists sp, (BV 64 0x151b4).
  rewrite /reg_col; cbn.
  iEval (rewrite /reg_col; cbn) in "Htmp Hsaved".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 &
      H27 & _)".
  iDestruct "H8" as (v8) "(%Hv8 & H8)".
  iDestruct "H9" as (v9) "(%Hv9 & H9)".
  iDestruct "H18" as (v18) "(%Hv18 & H18)".
  iDestruct "H19" as (v19) "(%Hv19 & H19)".
  iDestruct "H20" as (v20) "(%Hv20 & H20)".
  iDestruct "H21" as (v21) "(%Hv21 & H21)".
  iDestruct "H22" as (v22) "(%Hv22 & H22)".
  iDestruct "H23" as (v23) "(%Hv23 & H23)".
  iDestruct "H24" as (v24) "(%Hv24 & H24)".
  iDestruct "H25" as (v25) "(%Hv25 & H25)".
  iDestruct "H26" as (v26) "(%Hv26 & H26)".
  iDestruct "H27" as (v27) "(%Hv27 & H27)".
  cbn in Hv8, Hv9, Hv18, Hv19, Hv20, Hv21, Hv22, Hv23, Hv24, Hv25,
    Hv26, Hv27.
  subst v8; subst v9; subst v18; subst v19; subst v20; subst v21.
  subst v22; subst v23; subst v24; subst v25; subst v26; subst v27.
  iFrame.
  iSplit; first (iPureIntro; cbn; done).
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 48)).
  iSplitL "H10"; first iExact "H10".
  iExists (writeSuccessTransactionWord transaction 48). iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 56)).
  iSplitL "H11"; first iExact "H11".
  iExists (writeSuccessTransactionWord transaction 56). iSplit; first done.
  iExists (RVal_Bits b12). iSplitL "H12"; first iExact "H12".
  iExists b12. iSplit; first done.
  iExists (RVal_Bits b13). iSplitL "H13"; first iExact "H13".
  iExists b13. iSplit; first done.
  iExists (RVal_Bits b14). iSplitL "H14"; first iExact "H14".
  iExists b14. iSplit; first done.
  iExists (RVal_Bits b15). iSplitL "H15"; first iExact "H15".
  iExists b15. iSplit; first done.
  iExists (RVal_Bits b16). iSplitL "H16"; first iExact "H16".
  iExists b16. iSplit; first done.
  iExists (RVal_Bits b17). iSplitL "H17"; first iExact "H17".
  iExists b17. iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 192)).
  iFrame "H8". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 16)).
  iFrame "H9". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 48)).
  iFrame "H18". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 224)).
  iFrame "H19". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 56)).
  iFrame "H20". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 72)).
  iFrame "H21". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 200)).
  iFrame "H22". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 24)).
  iFrame "H23". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 8)).
  iFrame "H24". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 0)).
  iFrame "H25". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 184)).
  iFrame "H26". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits
    (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))).
  iFrame "H27". iSplit; first (iPureIntro; cbn; done).
  iFrame "H1 H2".
  iSplit; first (iPureIntro; exact Halign).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; exact Hbounds).
  iFrame "Hstack".
  iExists (writeSuccessTransactionPhaseEvents TransactionData sp transaction
    (writeSuccessTransactionsEvents sp remaining tail)).
  iEval (unfold writeSuccessTransactions151acCallRet,
    writeSuccessTransactions151acSaved) in "Hreturn".
  iFrame "Hmmio Htrace Hreturn".
Qed.
