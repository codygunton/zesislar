Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150fc.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Local Opaque
  WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_transaction_valid_frame
    `{!islaG Sigma} (transaction :
      WriteSuccessTransactionsSpec.writeSuccessTransaction) :
  WriteSuccessTransactionsSpec.writeSuccessTransactionOwn transaction -∗
  ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionValid transaction⌝ ∗
  WriteSuccessTransactionsSpec.writeSuccessTransactionOwn transaction.
Proof.
  rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionOwn.
  iIntros "(Hdata & Haccess & Hentries & Hblob & Hauthorization &
    %Hvalid & _)".
  iFrame. iPureIntro. naive_solver.
Qed.

Local Typeclasses Opaque
  WriteSuccessTransactionsSpec.writeSuccessTransactionOwn.

Definition writeSuccessTransactions150f0Frame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn processed ∗
   WriteSuccessTransactionsSpec.writeSuccessTransactionOwn transaction ∗
   WriteSuccessTransactionsSpec.writeSuccessTransactionsOwn remaining ∗ P ∗
   WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant
     sp base transactions processed (transaction :: remaining)
     bytes prefix suffix ∗
   instr_pre WriteSuccessTransactionsSpec.writeSuccessTransactionsLoopExitAddress
     (WriteSuccessTransactionsSpec.writeSuccessTransactionsLoopExit
       sp base transactions bytes tail P) ∗ True)%I.

#[local] Typeclasses Opaque writeSuccessTransactions150f0Frame.

Definition writeSuccessTransactionsAt150f0SomeBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (chainId sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (⌜WriteSuccessTransactionsSpec.writeSuccessTransactionChainId transaction =
      Some chainId⌝ ∗
   □ ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 <>
      BV 8 0⌝ ∗
   writeSuccessTransactionsMachine150f0
      sp base transactions processed transaction ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
      (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
        WriteSuccessTransactionsSpec.TransactionChainId sp transaction
        (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
          sp remaining tail)) ∗
   writeSuccessTransactions150f0Frame P sp base transaction transactions
      processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt150f0SomeBlock) := I.

Definition writeSuccessTransactionsAt150f0NoneBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (⌜WriteSuccessTransactionsSpec.writeSuccessTransactionChainId transaction =
      None⌝ ∗
   □ ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 =
      BV 8 0⌝ ∗
   writeSuccessTransactionsMachine150f0
      sp base transactions processed transaction ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
      (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
        WriteSuccessTransactionsSpec.TransactionChainId sp transaction
        (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
          sp remaining tail)) ∗
   writeSuccessTransactions150f0Frame P sp base transaction transactions
      processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt150f0NoneBlock) := I.

Definition writeSuccessTransactionsAt150f0ValidSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionValid transaction⌝ ∗
    writeSuccessTransactionsMachine150f0
      sp base transactions processed transaction ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
        WriteSuccessTransactionsSpec.TransactionChainId sp transaction
        (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
          sp remaining tail)) ∗
    writeSuccessTransactions150f0Frame P sp base transaction transactions
      processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt150f0ValidSpec) := I.

Definition writeSuccessTransactionsAt150f0SomeSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (chainId sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionChainId transaction =
      Some chainId⌝ ∗
    □ ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 <>
      BV 8 0⌝ ∗
    writeSuccessTransactionsMachine150f0
      sp base transactions processed transaction ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
        WriteSuccessTransactionsSpec.TransactionChainId sp transaction
        (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
          sp remaining tail)) ∗
    writeSuccessTransactions150f0Frame P sp base transaction transactions
      processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt150f0SomeSpec) := I.

Definition writeSuccessTransactionsAt150f0NoneSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionChainId transaction =
      None⌝ ∗
    □ ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 =
      BV 8 0⌝ ∗
    writeSuccessTransactionsMachine150f0
      sp base transactions processed transaction ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
        WriteSuccessTransactionsSpec.TransactionChainId sp transaction
        (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
          sp remaining tail)) ∗
    writeSuccessTransactions150f0Frame P sp base transaction transactions
      processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt150f0NoneSpec) := I.

Definition writeSuccessTransactions150f8OtherRegisters : list string :=
  ["x3"; "x4"; "x5"; "x6"; "x7";
   "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactionsMachine150f8
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     writeSuccessTransactions150f8OtherRegisters) ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x160f4) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 0x680)%bv ∗
   "x18" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 48) ∗
   "x19" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224) ∗
   "x20" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 56) ∗
   "x21" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 72) ∗
   "x22" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200) ∗
   "x23" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 184) ∗
   "x27" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32)) ∗
   WriteSuccessTransactionsBoundary150e8.writeSuccessTransactionsScratch150e8
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsMachine150f8) := I.

Definition writeSuccessTransactionsAt150f8SomeBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (chainId sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (⌜WriteSuccessTransactionsSpec.writeSuccessTransactionChainId transaction =
      Some chainId⌝ ∗
   □ ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 <>
      BV 8 0⌝ ∗
   writeSuccessTransactionsMachine150f8
      sp base transactions processed transaction ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
      (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
        WriteSuccessTransactionsSpec.TransactionChainId sp transaction
        (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
          sp remaining tail)) ∗
   writeSuccessTransactions150f0Frame P sp base transaction transactions
      processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt150f8SomeBlock) := I.

Definition writeSuccessTransactionsAt150f8NoneBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (⌜WriteSuccessTransactionsSpec.writeSuccessTransactionChainId transaction =
      None⌝ ∗
   □ ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 =
      BV 8 0⌝ ∗
   writeSuccessTransactionsMachine150f8
      sp base transactions processed transaction ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
      (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
        WriteSuccessTransactionsSpec.TransactionChainId sp transaction
        (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
          sp remaining tail)) ∗
   writeSuccessTransactions150f0Frame P sp base transaction transactions
      processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt150f8NoneBlock) := I.

Definition writeSuccessTransactionsAt150f8SomeSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (chainId sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionChainId transaction =
      Some chainId⌝ ∗
    □ ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 <>
      BV 8 0⌝ ∗
    writeSuccessTransactionsMachine150f8
      sp base transactions processed transaction ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
        WriteSuccessTransactionsSpec.TransactionChainId sp transaction
        (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
          sp remaining tail)) ∗
    writeSuccessTransactions150f0Frame P sp base transaction transactions
      processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt150f8SomeSpec) := I.

Definition writeSuccessTransactionsAt150f8NoneSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionChainId transaction =
      None⌝ ∗
    □ ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 =
      BV 8 0⌝ ∗
    writeSuccessTransactionsMachine150f8
      sp base transactions processed transaction ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
        WriteSuccessTransactionsSpec.TransactionChainId sp transaction
        (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
          sp remaining tail)) ∗
    writeSuccessTransactions150f0Frame P sp base transaction transactions
      processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt150f8NoneSpec) := I.

Lemma write_success_transactions_150f0_branch_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsAt150f0ValidSpec P -∗
  writeSuccessTransactionsAt150f0SomeSpec P ∨
  writeSuccessTransactionsAt150f0NoneSpec P.
Proof.
  rewrite /writeSuccessTransactionsAt150f0ValidSpec
    /writeSuccessTransactionsAt150f0SomeSpec
    /writeSuccessTransactionsAt150f0NoneSpec.
  iIntros "Hentry".
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining bytes prefix suffix tail)
    "(%Hvalid & Hmachine & Hmmio & Htrace & Hframe & _)".
  have HvalidParts := Hvalid.
  unfold WriteSuccessTransactionsSpec.writeSuccessTransactionValid in HvalidParts.
  destruct HvalidParts as (Hlen & Htype & HchainValid & Hrest).
  destruct
    (WriteSuccessTransactionsSpec.writeSuccessTransactionChainId transaction)
    as [chainId |] eqn:Hchain.
  - cbn in HchainValid. destruct HchainValid as [Htag Hword].
    iLeft. iExists chainId, sp, base, transaction, transactions, processed,
      remaining, bytes, prefix, suffix, tail.
    iFrame. repeat iSplit.
    + iPureIntro. exact Hchain.
    + iModIntro. iPureIntro. exact Htag.
  - cbn in HchainValid.
    iRight. iExists sp, base, transaction, transactions, processed,
      remaining, bytes, prefix, suffix, tail.
    iFrame. repeat iSplit.
    + iPureIntro. exact Hchain.
    + iModIntro. iPureIntro. exact HchainValid.
Qed.

Definition writeSuccessTransactionsAt150fcFramedSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine150fc
      sp base transactions processed transaction ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
        WriteSuccessTransactionsSpec.TransactionNonce sp transaction
        (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
          sp remaining tail)) ∗
    writeSuccessTransactions150f0Frame P sp base transaction transactions
      processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt150fcFramedSpec) := I.

Lemma write_success_transactions_150f0_valid_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsAt150f0Spec P -∗
  writeSuccessTransactionsAt150f0ValidSpec P.
Proof.
  rewrite /writeSuccessTransactionsAt150f0Spec
    /writeSuccessTransactionsAt150f0ValidSpec.
  iIntros "Hentry".
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining bytes prefix suffix tail)
    "Hhandoff".
  rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff.
  iDestruct "Hhandoff" as
    "(Hmachine & Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & Hinvariant & Hexit & _)".
  iPoseProof (write_success_transaction_valid_frame with "Htransaction")
    as "[%Hvalid Htransaction]".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  rewrite /writeSuccessTransactions150f0Frame.
  iFrame.
  iPureIntro. exact Hvalid.
Qed.

Lemma write_success_transactions_150fc_return_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsAt150fcFramedSpec P -∗
  writeSuccessTransactionsAt150fcSpec P.
Proof.
  rewrite /writeSuccessTransactionsAt150fcFramedSpec
    /writeSuccessTransactionsAt150fcSpec.
  iIntros "Hentry".
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining bytes prefix suffix tail)
    "(Hmachine & Hmmio & Htrace & Hframe & _)".
  iEval (unfold writeSuccessTransactions150f0Frame) in "Hframe".
  iDestruct "Hframe" as
    "(Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining & HP &
      Hinvariant & Hexit & _)".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff.
  iFrame.
Qed.
