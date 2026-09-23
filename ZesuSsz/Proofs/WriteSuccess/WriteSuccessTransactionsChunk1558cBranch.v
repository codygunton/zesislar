Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop HintsAuthorizationsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAuthorizationsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAuthorizationsInvariantIntro.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15584.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15620.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAuthorizationsAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1558cBranchLeaf.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessTransactions1558cHeld
    `{!islaG Sigma} (P : iProp Sigma) : iProp Sigma := P.

Lemma write_success_transactions_1558c_held_intro
    `{!islaG Sigma} (P : iProp Sigma) :
  P -∗ writeSuccessTransactions1558cHeld P.
Proof. move => *. zesu_block. Qed.

Lemma write_success_transactions_1558c_held_elim
    `{!islaG Sigma} (P : iProp Sigma) :
  writeSuccessTransactions1558cHeld P -∗ P.
Proof. move => *. zesu_block. Qed.

Global Opaque writeSuccessTransactions1558cHeld.

Lemma write_success_transactions_1558c_instruction :
  is_Some (IslaTraces.write_success_blocks.Index.lookup 0x1558c).
Proof. vm_compute. eauto. Qed.

Definition writeSuccessTransactions1558cFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (count : bv 64) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col writeSuccessTransactions1558cOtherRegShapes ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15584) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
    "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
    "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 240) ∗
    "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
    "x19" ↦ᵣ RVal_Bits pointer ∗
    "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗
    (bv_unsigned sp + 168) ↦ₘ
      writeSuccessTransactionWord transaction 240 ∗
    writeSuccessTransactionsAuthorizationsEntryFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    ⌜count = writeSuccessTransactionWord transaction 248⌝ ∗
    ⌜bv_unsigned pointer =
      (bv_unsigned (writeSuccessTransactionWord transaction 224) +
       32 * Z.of_nat
         (length (writeSuccessTransactionBlobHashes transaction)))%Z⌝ ∗
    True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactions1558cFrame) := I.

Lemma write_success_transactions_1558c_core_split
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsAt1558cCoreSpec P -∗
  ∃ count : bv 64,
    reg_col zesu_ram_sys_regs ∗ "x18" ↦ᵣ RVal_Bits count ∗
    writeSuccessTransactions1558cFrame P count ∗ True.
Proof.
  iIntros "(%sp & %pointer & %base & %transaction & %transactions &
    %processed & %remaining & %bytes & %prefix & %suffix & %tail &
    Hsys & Hregs & H1 & H2 & H5 & H8 & H9 & H10 & H11 & H18 & H19 &
    H22 & H168 & Hframe & %Hpointer & _)".
  iExists (writeSuccessTransactionWord transaction 248).
  iFrame "Hsys H18".
  iSplitL; last done.
  iExists sp, pointer, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame.
  repeat iSplit; try done.
Qed.

Lemma write_success_transaction_authorization_bounds
    `{!islaG Sigma} (transaction : writeSuccessTransaction) :
  ⌜writeSuccessTransactionAuthorizationBytes transaction <> []⌝ -∗
  writeSuccessTransactionOwn transaction -∗
  ⌜(mapRamBase defaultMap) <=
      bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction)⌝ ∗
  ⌜bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction) +
      Z.of_nat (length
        (writeSuccessTransactionAuthorizationBytes transaction)) <
      (machineRamEnd defaultMap)⌝ ∗
  writeSuccessTransactionOwn transaction.
Proof.
  iIntros (Hnonempty)
    "(Hdata & Haccess & Hentries & Hblob & Hauthorization & %Hvalid & _)".
  iEval (rewrite /writeSuccessByteArrayOwn) in "Hauthorization".
  destruct (writeSuccessTransactionAuthorizationBytes transaction)
    as [|byte authorization] eqn:Hbytes; first contradiction.
  iDestruct "Hauthorization" as "(Hbytes & %Hmin & %Hmax & _)".
  iSplit; first done. iSplit; first done.
  rewrite /writeSuccessTransactionOwn.
  iFrame "Hdata Haccess Hentries Hblob".
  iSplitL "Hbytes".
  - rewrite /writeSuccessByteArrayOwn Hbytes.
    iFrame "Hbytes".
    repeat iSplit; try done.
  - iSplit; first done. done.
Qed.

Lemma write_success_transactions_1558c_zero_destination
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_body 0x15620 (writeSuccessTransactionsAt15620Spec P) -∗
  instr_pre 0x15620
    (reg_col zesu_ram_sys_regs ∗ "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗
     writeSuccessTransactions1558cFrame P (BV 64 0)).
Proof.
  iIntros "Hnext".
  iApply (instr_pre_wand 0x15620 0x15620 false true with "Hnext");
    [done | done |].
  iIntros "(Hsys & H18 & Hframe)".
  iDestruct "Hframe" as
    "(%sp & %pointer & %base & %transaction & %transactions & %processed &
      %remaining & %bytes & %prefix & %suffix & %tail & Hregs & H1 & H2 &
      H5 & H8 & H9 & H10 & H11 & H19 & H22 & H168 & Hentry &
      %HcountWord & %Hpointer & _)".
  iDestruct "Hentry" as
    "(HscratchRestore & Hprefix & Hsuffix & Hprocessed & Htransaction &
      Hremaining & Hmmio & Htrace & HP & #Hinvariant & Hexit & _)".
  iPoseProof (write_success_transaction_own_valid with "Htransaction")
    as "[%Hvalid Htransaction]".
  have Hword240 : writeSuccessTransactionWord transaction 240 =
      writeSuccessTransactionAuthorizationPointer transaction.
  { unfold writeSuccessTransactionValid in Hvalid. naive_solver. }
  have Hcount : length (writeSuccessTransactionAuthorizations transaction) = 0%nat.
  { unfold writeSuccessTransactionValid in Hvalid.
    have Hunsigned :
        bv_unsigned (writeSuccessTransactionWord transaction 248) =
          Z.of_nat (length (writeSuccessTransactionAuthorizations transaction))
      by naive_solver.
    rewrite -HcountWord bv_unsigned_BV in Hunsigned.
    lia. }
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hregs".
  iDestruct "Hregs" as
    "(H3 & H4 & H6 & H7 & H12 & H13 & H14 & H15 & H16 & H17 &
      H20 & H21 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & _)".
  iAssert (reg_col writeSuccessTransactions15620OtherRegShapes)
    with "[H1 H3 H4 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17
      H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31]"
    as "HtargetRegs".
  { rewrite !reg_col_cons reg_col_nil.
    iFrame.
    repeat iSplit; iPureIntro; done. }
  iDestruct ("HscratchRestore" with "H168") as "Hscratch15564".
  iPoseProof (write_success_transactions_authorization_scratch_split
    sp base transactions processed transaction with
    "[] [] [] [] Hscratch15564") as "[HauthScratch HscratchRestore]".
  { iDestruct "Hinvariant" as
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & _ )".
    iPureIntro. exact Halign. }
  { iDestruct "Hinvariant" as
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & _ )".
    iPureIntro. lia. }
  { iDestruct "Hinvariant" as
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %Hmin & _ )".
    iPureIntro. lia. }
  { iDestruct "Hinvariant" as
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %Hmin & %Hmax & _)".
    iPureIntro. lia. }
  iDestruct ("HscratchRestore" with "HauthScratch") as "Hscratch".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  rewrite /writeSuccessTransactionPhaseHandoff
    /writeSuccessTransactionsProcessedOwn
    /writeSuccessTransactionsMachine15620.
  iFrame "Hsys HtargetRegs H2 H8 H9 H18 Hscratch Hprefix Hsuffix
    Hprocessed Htransaction Hremaining Hmmio HP Hexit".
  rewrite Hword240 Hcount /=.
  iFrame "Hinvariant".
  iSplit; first (iPureIntro; lia).
  iEval (rewrite /writeSuccessTransactionPhaseEvents /= Hcount /=) in "Htrace".
  iFrame "Htrace".
Qed.

Definition writeSuccessTransactionsAuthorizationsAnyLoopSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (authorizationSp : bv 64) (authorizationBase : Z)
      (authorizationTotal : nat) (authorizationBytes : list (bv 8))
      (authorizationTail : spec),
    writeSuccessAuthorizationsLoopSpec
      (writeSuccessTransactionsAuthorizationsFrame authorizationSp
        authorizationBase authorizationTotal authorizationBytes
        authorizationTail P))%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAuthorizationsAnyLoopSpec) := I.

Lemma write_success_transactions_1558c_nonzero_destination
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) (count : bv 64)
    (Hcount : count <> BV 64 0) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15590
    (writeSuccessTransactionsAuthorizationsAnyLoopSpec P) -∗
  instr_body 0x15620 (writeSuccessTransactionsAt15620Spec P) -∗
  instr_pre 0x15590
    (reg_col zesu_ram_sys_regs ∗ "x18" ↦ᵣ RVal_Bits count ∗
     writeSuccessTransactions1558cFrame P count).
Proof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Hu256 #Hint #Houtput #Hloop Hnext".
  iApply (instr_pre_wand 0x15590 0x15590 true true with "Hloop");
    [done | done |].
  iIntros "(Hsys & H18 & Hframe)".
  iDestruct "Hframe" as
    "(%sp & %pointer & %base & %transaction & %transactions & %processed &
      %remaining & %bytes & %prefix & %suffix & %tail & Hregs & H1 & H2 &
      H5 & H8 & H9 & H10 & H11 & H19 & H22 & H168 & Hentry &
      %HcountWord & %Hpointer & _)".
  iDestruct "Hentry" as
    "(HscratchRestore & Hprefix & Hsuffix & Hprocessed & Htransaction &
      Hremaining & Hmmio & Htrace & HP & #Hinvariant & Hexit & _)".
  iAssert (writeSuccessTransactions1558cHeld
      (spec_trace
        (writeSuccessTransactionPhaseEvents TransactionAuthorizations sp
          transaction (writeSuccessTransactionsEvents sp remaining tail))))
    with "[Htrace]" as "HtraceHeld".
  { iApply write_success_transactions_1558c_held_intro. iExact "Htrace". }
  iPoseProof (write_success_transaction_own_valid with "Htransaction")
    as "[%Hvalid Htransaction]".
  have Hword240 : writeSuccessTransactionWord transaction 240 =
      writeSuccessTransactionAuthorizationPointer transaction.
  { unfold writeSuccessTransactionValid in Hvalid. naive_solver. }
  have HallAuthorizationLengths :
      Forall (fun item => length item = 144%nat)
        (writeSuccessTransactionAuthorizations transaction).
  { unfold writeSuccessTransactionValid in Hvalid. naive_solver. }
  have HauthorizationCountUnsigned :
      bv_unsigned (writeSuccessTransactionWord transaction 248) =
        Z.of_nat (length (writeSuccessTransactionAuthorizations transaction)).
  { unfold writeSuccessTransactionValid in Hvalid. naive_solver. }
  destruct (writeSuccessTransactionAuthorizations transaction)
    as [|authorization authorizations] eqn:Hauthorizations.
  { exfalso. apply Hcount. apply bv_eq.
    unfold writeSuccessTransactionValid in Hvalid.
    have HunsignedWord :
        bv_unsigned (writeSuccessTransactionWord transaction 248) =
          Z.of_nat (length (writeSuccessTransactionAuthorizations transaction))
      by naive_solver.
    rewrite Hauthorizations /= in HunsignedWord.
    have Hunsigned : bv_unsigned count = 0%Z by
      rewrite HcountWord; exact HunsignedWord.
    rewrite bv_unsigned_BV. exact Hunsigned. }
  have HauthorizationLengths :
      Forall (fun item => length item = 144%nat)
        (authorization :: authorizations).
  { exact HallAuthorizationLengths. }
  have HbytesLength :
      length (writeSuccessTransactionAuthorizationBytes transaction) =
        (144 * S (length authorizations))%nat.
  { rewrite /writeSuccessTransactionAuthorizationBytes Hauthorizations.
    apply write_success_fixed_lists_concat_length.
    exact HauthorizationLengths. }
  have HbytesNonempty :
      writeSuccessTransactionAuthorizationBytes transaction <> [].
  { intros Hempty. rewrite Hempty in HbytesLength. simpl in HbytesLength. lia. }
  have HcountValue :
      count = Z_to_bv 64 (Z.of_nat (S (length authorizations))).
  { apply bv_eq. rewrite Z_to_bv_unsigned.
    rewrite HcountWord.
    rewrite (bv_wrap_small 64 (Z.of_nat (S (length authorizations))));
      first exact HauthorizationCountUnsigned.
    have HcountRange := bv_unsigned_in_range 64
      (writeSuccessTransactionWord transaction 248).
    rewrite HauthorizationCountUnsigned in HcountRange.
    simpl in HcountRange. lia. }
  iPoseProof (write_success_transaction_authorization_bounds transaction with
    "[] Htransaction") as "(%HauthMin & %HauthMax & Htransaction)".
  { iPureIntro. exact HbytesNonempty. }
  iPoseProof (write_success_transaction_authorization_split transaction with
    "[] Htransaction") as "[HauthBytes HtransactionRestore]".
  { iPureIntro. exact HbytesNonempty. }
  iDestruct ("HscratchRestore" with "H168") as "Hscratch15564".
  iPoseProof (write_success_transactions_authorization_scratch_split
    sp base transactions processed transaction with
    "[] [] [] [] Hscratch15564") as "[HauthScratch HscratchRestore]".
  { iDestruct "Hinvariant" as
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & _)".
    iPureIntro. exact Halign. }
  { iDestruct "Hinvariant" as
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & _)".
    iPureIntro. lia. }
  { iDestruct "Hinvariant" as
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %Hmin & _)".
    iPureIntro. lia. }
  { iDestruct "Hinvariant" as
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %Hmin & %Hmax & _)".
    iPureIntro. lia. }
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hregs".
  iDestruct "Hregs" as
    "(H3 & H4 & H6 & H7 & H12 & H13 & H14 & H15 & H16 & H17 &
      H20 & H21 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & _)".
  iAssert (reg_col writeSuccessAuthorizationsOtherRegShapes)
    with "[H1 H3 H4 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17
      H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31]"
    as "HauthRegs".
  { rewrite !reg_col_cons reg_col_nil.
    iFrame. repeat iSplit; iPureIntro; done. }
  iExists sp,
    (bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction)),
    (S (length authorizations)),
    (writeSuccessTransactionAuthorizationBytes transaction),
    (writeSuccessTransactionPhaseEvents TransactionV sp transaction
      (writeSuccessTransactionsEvents sp remaining tail)).
  rewrite /writeSuccessAuthorizationsLoopSpec.
  iExists sp, (writeSuccessTransactionAuthorizationPointer transaction),
    (bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction)),
    (S (length authorizations)), 0%nat, (length authorizations),
    (writeSuccessTransactionAuthorizationBytes transaction), [],
    (writeSuccessTransactionAuthorizationBytes transaction),
    (writeSuccessTransactionPhaseEvents TransactionV sp transaction
      (writeSuccessTransactionsEvents sp remaining tail)).
  rewrite HcountValue Hword240.
  iSplitL "Hsys"; first iExact "Hsys".
  iSplitL "HauthRegs"; first iExact "HauthRegs".
  iSplitL "H2"; first iExact "H2".
  iSplitL "H8"; first iExact "H8".
  iSplitL "H9"; first iExact "H9".
  iSplitL "H18"; first iExact "H18".
  iSplitL "".
  { rewrite mem_mapsto_array_eq /mem_mapsto_array_def.
    iExists 1%N. simpl. repeat iSplit; iPureIntro; lia. }
  iSplitL "HauthBytes"; first iExact "HauthBytes".
  iSplitL "HauthScratch"; first iExact "HauthScratch".
  iSplitL "Hmmio"; first iExact "Hmmio".
  iSplitL "HtraceHeld".
  { iPoseProof (write_success_transactions_1558c_held_elim with
      "HtraceHeld") as "Htrace".
    iEval (rewrite /writeSuccessTransactionPhaseEvents /= Hauthorizations /=)
      in "Htrace".
    iExact "Htrace". }
  iSplitL "HscratchRestore HtransactionRestore Hprefix Hsuffix Hprocessed
    Hremaining HP Hinvariant Hexit".
  { rewrite /writeSuccessTransactionsAuthorizationsFrame.
    iExists sp, base, transaction, transactions, processed, remaining,
      bytes, prefix, suffix, tail.
    iFrame.
    iFrame "Hinvariant".
    repeat iSplit; try done.
    rewrite Hauthorizations. done. }
  have HauthorizationBound :
      (S (length authorizations) < 2 ^ 64)%nat.
  { have Hrange := bv_unsigned_in_range 64
      (writeSuccessTransactionWord transaction 248).
    rewrite HauthorizationCountUnsigned in Hrange.
    unfold bv_modulus in Hrange.
    cbn in Hrange.
    apply (proj2 (Nat2Z.inj_lt _ _)).
    rewrite Nat2Z.inj_pow.
    exact (proj2 Hrange). }
  iPoseProof "Hinvariant" as "#HinvariantFacts".
  iDestruct "HinvariantFacts" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %HspMin &
      %HspMax & _)".
  iSplitL "".
  { iApply (write_success_authorizations_invariant_zero_intro sp
      (writeSuccessTransactionAuthorizationPointer transaction)
      (length authorizations)
      (writeSuccessTransactionAuthorizationBytes transaction));
      try done; lia. }
  iPoseProof (write_success_transactions_authorizations_exit
    sp (bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction))
    (S (length authorizations))
    (writeSuccessTransactionAuthorizationBytes transaction)
    (writeSuccessTransactionPhaseEvents TransactionV sp transaction
      (writeSuccessTransactionsEvents sp remaining tail)) P with "Hnext")
    as "Hexit".
  iFrame "Hexit".
Qed.

Lemma write_success_transactions_chunk_1558c_branch
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15590
    (writeSuccessTransactionsAuthorizationsAnyLoopSpec P) -∗
  instr_body 0x15620 (writeSuccessTransactionsAt15620Spec P) -∗
  instr_body 0x1558c (writeSuccessTransactionsAt1558cCoreSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hmemcpy #Hu256 #Hint #Houtput #Hauthloop Hnext".
  iPoseProof "Hlookup" as "#HrawLookup".
  iEval (rewrite /instr_lookup_resources) in "HrawLookup".
  iPoseProof ("HrawLookup" $! 0x1558c with "[]") as "#HbranchCode".
  { iPureIntro. exact write_success_transactions_1558c_instruction. }
  iPoseProof (write_success_transactions_chunk_1558c_branch_leaf
    (fun count => writeSuccessTransactions1558cFrame P count)
    with "HbranchCode") as "Hleaf".
  iApply (instr_pre_wand 0x1558c 0x1558c false false with "Hleaf");
    [done | done |].
  iIntros "Hcore".
  iPoseProof (write_success_transactions_1558c_core_split P with "Hcore")
    as "(%count & Hsys & H18 & Hframe & _)".
  destruct (decide (count = BV 64 0)) as [Hcount | Hcount].
  - subst count. iLeft.
    rewrite /writeSuccessTransactionsAt1558cZeroLeafSpec.
    iFrame.
    iSplit; last done.
    iApply (write_success_transactions_1558c_zero_destination P with "Hnext").
  - iRight. iExists count. iSplit; first done.
    rewrite /writeSuccessTransactionsAt1558cNonzeroLeafSpec.
    iFrame.
    iSplit; last done.
    iApply (write_success_transactions_1558c_nonzero_destination P count Hcount
      with "Hlookup Hcode Hmemcpy Hu256 Hint Houtput Hauthloop Hnext").
Qed.
