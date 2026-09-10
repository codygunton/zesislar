From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressNone15198Machine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsOptionalAddressNone15198CallRet
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (transaction : writeSuccessTransaction) (remaining : list writeSuccessTransaction)
    (tail : spec) : iProp Sigma :=
  zesu_c_call_ret 16
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
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))]
    (BV 64 0x1519c) sp
    (fun _ =>
      mmio_range 0x2401a0c0 16 ∗
      spec_trace
        (writeSuccessTransactionPhaseEvents TransactionValue sp transaction
          (writeSuccessTransactionsEvents sp remaining tail)) ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsOptionalAddressNone15198CallRet) := I.

Definition writeSuccessTransactionsOptionalAddressNone15198ReturnFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col writeSuccessTransactions150e8OtherRegShapes ∗
   base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsProcessedOwn processed ∗
   writeSuccessTransactionOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗
   P ∗
   writeSuccessTransactionsInvariant
     sp base transactions processed (transaction :: remaining)
     bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit sp base transactions bytes tail P) ∗
   ((bv_unsigned sp - 16) ↦ₘ? 16 -∗
      writeSuccessTransactionsScratch150e8
        sp base transactions processed transaction) ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsOptionalAddressNone15198ReturnFrame) := I.

Lemma write_success_transactions_optional_address_none_15198_return_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsOptionalAddressNone15198CallRet
      sp transaction remaining tail -∗
  ⌜writeSuccessTransactionTo transaction = None⌝ -∗
  writeSuccessTransactionsOptionalAddressNone15198ReturnFrame P sp base
    transaction transactions processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsAt1519cSpec P.
Proof.
  iStartProof. iIntros "Hpost Hto Hframe".
  iDestruct "Hto" as %Hto.
  iEval (unfold writeSuccessTransactionsOptionalAddressNone15198ReturnFrame)
    in "Hframe".
  iDestruct "Hframe" as
    "(Hother & Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining &
      HP & Hinv & Hexit & HscratchFrame & _)".
  iEval (unfold writeSuccessTransactionsOptionalAddressNone15198CallRet,
    zesu_c_call_ret) in "Hpost".
  iDestruct "Hpost" as "(HsysPost & Hcaller & Hsaved & Hrest)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hcaller Hsaved".
  iDestruct "Hcaller" as
    "(H1Post & H12Post & H13Post & H14Post & H15Post & H16Post & H17Post &
      H5Post & H6Post & H7Post & H28Post & H29Post & H30Post & H31Post & _)".
  iDestruct "Hsaved" as
    "(H8Raw & H9Raw & H18Raw & H19Raw & H20Raw & H21Raw & H22Raw &
      H23Raw & H24Raw & H25Raw & H26Raw & H27Raw & _)".
  iDestruct "H8Raw" as (v8) "(%Hv8 & H8Post)".
  iDestruct "H9Raw" as (v9) "(%Hv9 & H9Post)".
  iDestruct "H18Raw" as (v18) "(%Hv18 & H18Post)".
  iDestruct "H19Raw" as (v19) "(%Hv19 & H19Post)".
  iDestruct "H20Raw" as (v20) "(%Hv20 & H20Post)".
  iDestruct "H21Raw" as (v21) "(%Hv21 & H21Post)".
  iDestruct "H22Raw" as (v22) "(%Hv22 & H22Post)".
  iDestruct "H23Raw" as (v23) "(%Hv23 & H23Post)".
  iDestruct "H24Raw" as (v24) "(%Hv24 & H24Post)".
  iDestruct "H25Raw" as (v25) "(%Hv25 & H25Post)".
  iDestruct "H26Raw" as (v26) "(%Hv26 & H26Post)".
  iDestruct "H27Raw" as (v27) "(%Hv27 & H27Post)".
  cbn in Hv8, Hv9, Hv18, Hv19, Hv20, Hv21, Hv22, Hv23, Hv24, Hv25,
    Hv26, Hv27.
  subst v8; subst v9; subst v18; subst v19; subst v20; subst v21.
  subst v22; subst v23; subst v24; subst v25; subst v26; subst v27.
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10Post & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)". subst r10.
  iDestruct "Hrest" as (r11) "(H11Post & Hrest)".
  iDestruct "Hrest" as (b11)
    "(%Hr11 & H2Post & HstackReturn & Hmmio & Htrace & _)". subst r11.
  iAssert (reg_col [(KindReg "x10", BitsShape 64);
    (KindReg "x11", BitsShape 64)])%I with "[H10Post H11Post]" as
    "Houtputs".
  { rewrite !reg_col_cons reg_col_nil.
    iSplitL "H10Post".
    - iExists (RVal_Bits b10).
      iSplit; [iPureIntro; cbn; done | iFrame].
    - iSplitL "H11Post".
      + iExists (RVal_Bits b11).
        iSplit; [iPureIntro; cbn; done | iFrame].
      + done. }
  iDestruct "H5Post" as (v5) "(%Hv5 & H5Post)".
  iAssert ("x5" ↦ᵣ: fun value =>
      ⌜valu_has_shape value (BitsShape 64)⌝)%I
    with "[H5Post]" as "H5Target".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists v5. iSplitL "H5Post"; [iExact "H5Post"|].
    iPureIntro. exact Hv5. }
  iPoseProof ("HscratchFrame" with "HstackReturn") as "Hscratch".
  iAssert (writeSuccessTransactionsMachine1519c
      sp base transactions processed transaction)
    with "[HsysPost Hother H1Post H2Post H5Target H6Post H7Post Houtputs
      H8Post H9Post H12Post H13Post H14Post H15Post H16Post H17Post
      H18Post H19Post H20Post H21Post H22Post H23Post H24Post H25Post
      H26Post H27Post H28Post H29Post H30Post H31Post Hscratch]" as
    "Hmachine".
  { iApply (write_success_transactions_optional_address_none_15198_machine
      sp base transactions processed transaction Hto with "HsysPost Hother H1Post
      H2Post H5Target H6Post H7Post Houtputs H8Post H9Post H12Post H13Post
      H14Post H15Post H16Post H17Post H18Post H19Post H20Post H21Post H22Post
      H23Post H24Post H25Post H26Post H27Post H28Post H29Post H30Post H31Post
      Hscratch"). }
  iFrame "Hprefix Hsuffix Hprocessed Htransaction Hremaining Hmmio Htrace HP
    Hinv Hexit Hmachine".
Qed.
