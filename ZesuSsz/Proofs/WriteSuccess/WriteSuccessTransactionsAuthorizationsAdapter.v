From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAuthorizationsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15564.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15584.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15620.

Lemma write_success_fixed_lists_concat_length
    (width : nat) (lists : list (list (bv 8))) :
  Forall (fun bytes => length bytes = width) lists ->
  length (concat lists) = (width * length lists)%nat.
Proof.
  induction lists as [|bytes lists IH]; inversion 1; simpl; [done |].
  rewrite app_length H2 IH; [lia | done].
Qed.

Lemma write_success_transaction_own_valid
    `{!islaG Sigma} (transaction : writeSuccessTransaction) :
  writeSuccessTransactionOwn transaction -∗
  ⌜writeSuccessTransactionValid transaction⌝ ∗
  writeSuccessTransactionOwn transaction.
Proof.
  iIntros "(Hdata & Haccess & Hentries & Hblob & Hauthorization &
    %Hvalid & _)".
  iFrame.
  iSplit; done.
Qed.

Lemma write_success_transactions_15584_load_split
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
  writeSuccessTransactionsScratch15564
      sp base transactions processed transaction -∗
  (bv_unsigned sp + 168) ↦ₘ
      writeSuccessTransactionWord transaction 240 ∗
  ((bv_unsigned sp + 168) ↦ₘ
      writeSuccessTransactionWord transaction 240 -∗
   writeSuccessTransactionsScratch15564
      sp base transactions processed transaction).
Proof.
  iIntros "(Hlower32 & Hlower16 & H0 & H104 & H112 & H120 & H128 &
    H136 & H144 & H152 & H160 & H168 & H176 & H184 & H192 & H200 &
    H208 & H216 & H224 & H232 & H240 & H248 & H256 & H264 & H272 &
    H280 & H1680 & H1712 & _)".
  iFrame "H168".
  iIntros "H168".
  rewrite /writeSuccessTransactionsScratch15564
    /writeSuccessTransactionsScratch15564Frame.
  iFrame.
Qed.

Definition writeSuccessTransactionsAuthorizationsEntryFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (((bv_unsigned sp + 168) ↦ₘ
       writeSuccessTransactionWord transaction 240 -∗
     writeSuccessTransactionsScratch15564
       sp base transactions processed transaction) ∗
   base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsOwn processed ∗
   writeSuccessTransactionOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeSuccessTransactionPhaseEvents TransactionAuthorizations sp
       transaction (writeSuccessTransactionsEvents sp remaining tail)) ∗
   P ∗
   writeSuccessTransactionsInvariant sp base transactions processed
     (transaction :: remaining) bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit
       sp base transactions bytes tail P) ∗ True)%I.

Definition writeSuccessTransactionsAt15584CoreSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessTransactions15584OtherRegShapes ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15584) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
    "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 248) ∗
    "x19" ↦ᵣ RVal_Bits pointer ∗
    "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗
    (bv_unsigned sp + 168) ↦ₘ
      writeSuccessTransactionWord transaction 240 ∗
    writeSuccessTransactionsAuthorizationsEntryFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp + 168 < 0x40000000⌝ ∗
    ⌜bv_unsigned pointer =
      (bv_unsigned (writeSuccessTransactionWord transaction 224) +
       32 * Z.of_nat
         (length (writeSuccessTransactionBlobHashes transaction)))%Z⌝ ∗
    True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt15584CoreSpec) := I.

Definition writeSuccessTransactions1558cOtherRegisters : list string :=
  ["x3"; "x4"; "x6"; "x7";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x20"; "x21"; "x23"; "x24"; "x25"; "x26"; "x27";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactions1558cOtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactions1558cOtherRegisters.

Definition writeSuccessTransactionsAt1558cCoreSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessTransactions1558cOtherRegShapes ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15584) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
    "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 240) ∗
    "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
    "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 248) ∗
    "x19" ↦ᵣ RVal_Bits pointer ∗
    "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗
    (bv_unsigned sp + 168) ↦ₘ
      writeSuccessTransactionWord transaction 240 ∗
    writeSuccessTransactionsAuthorizationsEntryFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    ⌜bv_unsigned pointer =
      (bv_unsigned (writeSuccessTransactionWord transaction 224) +
       32 * Z.of_nat
         (length (writeSuccessTransactionBlobHashes transaction)))%Z⌝ ∗
    True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt1558cCoreSpec) := I.

Definition writeSuccessTransactionsAt1558cZeroSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ count : bv 64,
      ⌜count = BV 64 0⌝ ∗
      reg_col zesu_ram_sys_regs ∗
      "x18" ↦ᵣ RVal_Bits count ∗
      instr_pre 0x15620
        (reg_col zesu_ram_sys_regs ∗ "x18" ↦ᵣ RVal_Bits count) ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt1558cZeroSpec) := I.

Definition writeSuccessTransactionsAt1558cNonzeroSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ count : bv 64,
      ⌜count <> BV 64 0⌝ ∗
      reg_col zesu_ram_sys_regs ∗
      "x18" ↦ᵣ RVal_Bits count ∗
      instr_pre 0x15590
        (reg_col zesu_ram_sys_regs ∗ "x18" ↦ᵣ RVal_Bits count) ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt1558cNonzeroSpec) := I.

Definition writeSuccessTransactionsAt1558cReadySpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (writeSuccessTransactionsAt1558cZeroSpec P ∨
   writeSuccessTransactionsAt1558cNonzeroSpec P)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt1558cReadySpec) := I.

Lemma write_success_transactions_15584_entry_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsAt15584Spec P -∗
  writeSuccessTransactionsAt15584CoreSpec P.
Proof.
  iIntros "(%sp & %base & %transaction & %transactions & %processed &
    %remaining & %bytes & %prefix & %suffix & %tail & Hphase)".
  iDestruct "Hphase" as
    "((%pointer & Hsys & Hregs & H1 & H2 & H5 & H10 & H11 & H18 &
      H19 & H22 & Hscratch & %Hpointer & _) & Hprefix & Hsuffix &
      Hprocessed & Htransaction & Hremaining & Hmmio & Htrace & HP &
      Hinvariant & Hexit & _)".
  iPoseProof (write_success_transactions_15584_load_split with "Hscratch")
    as "[H168 HscratchRestore]".
  iDestruct "Hinvariant" as "#Hinvariant".
  iPoseProof "Hinvariant" as "HinvariantCopy".
  iDestruct "HinvariantCopy" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign16 &
      %HspMin & %HspMax & _)".
  have Halign8 : bv_unsigned sp `mod` 8 = 0 by lia.
  have HloadBounds :
      0x20000000 <= bv_unsigned sp + 168 < 0x40000000 by lia.
  iEval (unfold writeSuccessTransactionsProcessedOwn) in "Hprocessed".
  iAssert (writeSuccessTransactionsAuthorizationsEntryFrame P sp base
      transaction transactions processed remaining bytes prefix suffix tail)
    with "[HscratchRestore Hprefix Hsuffix Hprocessed Htransaction
      Hremaining Hmmio Htrace HP Hinvariant Hexit]" as "Hframe".
  { rewrite /writeSuccessTransactionsAuthorizationsEntryFrame.
    iFrame.
    iExact "Hinvariant". }
  iExists sp, pointer, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "Hsys Hregs H1 H2 H5 H10 H11 H18 H19 H22 H168 Hframe".
  repeat iSplit; try done.
  all: iPureIntro; lia.
Qed.

Lemma write_success_transactions_authorization_scratch_split
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
  ⌜bv_unsigned sp `mod` 16 = 0⌝ -∗
  ⌜bv_unsigned sp `mod` 8 = 0⌝ -∗
  ⌜0x20000000 <= bv_unsigned sp - 48⌝ -∗
  ⌜bv_unsigned sp + 1896 < 0x40000000⌝ -∗
  writeSuccessTransactionsScratch15564
      sp base transactions processed transaction -∗
  writeSuccessAuthorizationsScratch sp ∗
  (writeSuccessAuthorizationsScratch sp -∗
   writeSuccessTransactionsScratch15620
      sp base transactions processed transaction).
Proof.
  iIntros "%Halign16 %Halign8 %HspMin %HspMax
    (Hlower32 & Hlower16 & H0 & H104 & H112 & H120 & H128 &
    H136 & H144 & H152 & H160 & H168 & H176 & H184 & H192 & H200 &
    H208 & H216 & H224 & H232 & H240 & H248 & H256 & H264 & H272 &
    H280 & H1680 & Hupper & _)".
  iDestruct (mem_mapsto_uninit_split 32 with "Hupper") as
    "[H1712 Hupper]"; first lia.
  iDestruct (mem_mapsto_uninit_split 144 with "Hupper") as
    "[H1744 H1888]"; first lia.
  have H1744Address :
      bv_unsigned sp + 1712 + 32 = bv_unsigned sp + 1744 by lia.
  have H1888Address :
      bv_unsigned sp + 1712 + 32 + 144 = bv_unsigned sp + 1888 by lia.
  iEval (rewrite H1744Address) in "H1744".
  iEval (rewrite H1888Address) in "H1888".
  have HlowerAddress :
      bv_unsigned sp - 32 = bv_unsigned sp - 48 + 16 by lia.
  iEval (rewrite HlowerAddress) in "Hlower32".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I
    with "[Hlower16 Hlower32]" as "Hlower48".
  { iApply (mem_mapsto_uninit_combine 16 with
      "[Hlower16] [Hlower32]");
      [lia | iExact "Hlower16" | iExact "Hlower32"]. }
  iSplitL "Hlower48 H1744".
  { rewrite /writeSuccessAuthorizationsScratch. iFrame. }
  iIntros "(Hlower48 & H1744 & _)".
  have H1680Address :
      bv_unsigned sp + 1680 = bv_unsigned sp + 280 + 1400 by lia.
  have H1712Address :
      bv_unsigned sp + 1712 = bv_unsigned sp + 280 + 1432 by lia.
  iEval (rewrite H1680Address) in "H1680".
  iEval (rewrite H1712Address) in "H1712".
  iAssert ((bv_unsigned sp + 280) ↦ₘ? 1464)%I
    with "[H280 H1680 H1712]" as "Hmiddle".
  { iAssert ((bv_unsigned sp + 280) ↦ₘ? 1432)%I
      with "[H280 H1680]" as "H1432".
    { iApply (mem_mapsto_uninit_combine 1400 with
        "[H280] [H1680]");
        [lia | iExact "H280" | iExact "H1680"]. }
    iApply (mem_mapsto_uninit_combine 1432 with
      "[H1432] [H1712]");
      [lia | iExact "H1432" | iExact "H1712"]. }
  rewrite /writeSuccessTransactionsScratch15620
    /writeSuccessTransactionsScratch15620Tail.
  iFrame.
  repeat iSplit; try done.
Qed.

Lemma write_success_transaction_authorization_split
    `{!islaG Sigma} (transaction : writeSuccessTransaction) :
  ⌜writeSuccessTransactionAuthorizationBytes transaction <> []⌝ -∗
  writeSuccessTransactionOwn transaction -∗
  bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction) ↦ₘ∗
      writeSuccessTransactionAuthorizationBytes transaction ∗
  (bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction) ↦ₘ∗
      writeSuccessTransactionAuthorizationBytes transaction -∗
   writeSuccessTransactionOwn transaction).
Proof.
  iIntros (Hnonempty)
    "(Hdata & Haccess & Hentries & Hblob & Hauthorization & %Hvalid & _)".
  iEval (rewrite /writeSuccessByteArrayOwn) in "Hauthorization".
  destruct (writeSuccessTransactionAuthorizationBytes transaction)
    as [|byte authorization] eqn:HauthBytesEq; first contradiction.
  iDestruct "Hauthorization" as
    "(HauthBytes & %Hmin & %Hmax & _)".
  iFrame "HauthBytes".
  iIntros "HauthBytes".
  rewrite /writeSuccessTransactionOwn.
  iFrame "Hdata Haccess Hentries Hblob".
  iSplitL "HauthBytes".
  { rewrite /writeSuccessByteArrayOwn HauthBytesEq.
    iFrame.
    repeat iSplit; try done. }
  iSplit; first done.
  done.
Qed.

Definition writeSuccessTransactionsAuthorizationsFrame
    `{!islaG Sigma} `{!threadG}
    (authorizationSp : bv 64) (authorizationBase : Z)
    (authorizationTotal : nat)
    (authorizationBytes : list (bv 8)) (authorizationTail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    (writeSuccessAuthorizationsScratch sp -∗
      writeSuccessTransactionsScratch15620
        sp base transactions processed transaction) ∗
    (bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction)
       ↦ₘ∗ writeSuccessTransactionAuthorizationBytes transaction -∗
      writeSuccessTransactionOwn transaction) ∗
    base ↦ₘ∗ prefix ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
    writeSuccessTransactionsOwn processed ∗
    writeSuccessTransactionsOwn remaining ∗ P ∗
    writeSuccessTransactionsInvariant sp base transactions processed
      (transaction :: remaining) bytes prefix suffix ∗
    instr_pre writeSuccessTransactionsLoopExitAddress
      (writeSuccessTransactionsLoopExit
        sp base transactions bytes tail P) ∗
    ⌜writeSuccessTransactionWord transaction 240 =
      writeSuccessTransactionAuthorizationPointer transaction⌝ ∗
    ⌜authorizationSp = sp⌝ ∗
    ⌜authorizationBase =
      bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction)⌝ ∗
    ⌜authorizationTotal =
      length (writeSuccessTransactionAuthorizations transaction)⌝ ∗
    ⌜authorizationBytes =
      writeSuccessTransactionAuthorizationBytes transaction⌝ ∗
    ⌜authorizationTail =
      writeSuccessTransactionPhaseEvents TransactionV sp transaction
        (writeSuccessTransactionsEvents sp remaining tail)⌝ ∗ True)%I.

Lemma write_success_transactions_authorizations_exit
    `{!islaG Sigma} `{!threadG}
    (authorizationSp : bv 64) (authorizationBase : Z)
    (authorizationTotal : nat)
    (authorizationBytes : list (bv 8)) (authorizationTail : spec)
    (P : iProp Sigma) :
  instr_body 0x15620 (writeSuccessTransactionsAt15620Spec P) -∗
  instr_pre 0x15620
    (writeSuccessAuthorizationsLoopExit authorizationSp authorizationBase
      authorizationTotal authorizationBytes authorizationTail
      (writeSuccessTransactionsAuthorizationsFrame authorizationSp
        authorizationBase
        authorizationTotal authorizationBytes authorizationTail P)).
Proof.
  iIntros "Hnext".
  iApply (instr_pre_wand 0x15620 0x15620 false true with "Hnext");
    [done | done |].
  iIntros "(%pointer & Hsys & Hregs & H2 & H8 & H9 & H18 & HauthBytes &
    HauthScratch & Hmmio & Htrace & Hframe & %Hpointer & _)".
  iDestruct "Hframe" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & HscratchRestore &
      HtransactionRestore & Hprefix & Hsuffix & Hprocessed & Hremaining &
      HP & Hinvariant & Hexit & %Hword240 & %Hsp & %Hbase & %Htotal &
      %Hbytes & %Htail & _)".
  subst authorizationSp authorizationBase authorizationTotal authorizationBytes
    authorizationTail.
  iDestruct ("HscratchRestore" with "HauthScratch") as "Hscratch".
  iDestruct ("HtransactionRestore" with "HauthBytes") as "Htransaction".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  rewrite /writeSuccessTransactionPhaseHandoff
    /writeSuccessTransactionsMachine15620.
  iFrame.
  rewrite Hword240.
  iFrame.
  iSplit; first done.
  done.
Qed.
