From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary10190.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150ecCall.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsMachine150e8Rest
  writeSuccessTransactions150ecCallFrame.

Definition writeSuccessTransactionsAt150ecJumpBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x100e8) ∗
   writeSuccessTransactionsMachine150e8Rest
     sp base transactions processed transaction ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 1)
       (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
         (writeSuccessTransactionsEvents sp remaining tail))) ∗
   writeSuccessTransactions150ecCallFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Definition writeSuccessTransactionsAt10190Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x150f0) ∗
   writeSuccessTransactionsMachine150e8Rest
     sp base transactions processed transaction ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 1)
       (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
         (writeSuccessTransactionsEvents sp remaining tail))) ∗
     writeSuccessTransactions150ecCallFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt150ecJumpBlock) := I.
Global Instance : LithiumUnfold (@writeSuccessTransactionsAt10190Block) := I.

Lemma write_success_transactions_chunk_150ec_jump_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_pre 0x10190 (writeSuccessTransactionsAt10190Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail) -∗
  instr_body 0x150ec (writeSuccessTransactionsAt150ecJumpBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: repeat iIntros "?"; liARun.
Qed.

Lemma write_success_transactions_chunk_150ec_jump
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_pre 0x10190 (writeSuccessTransactionsAt10190Spec P) -∗
  instr_body 0x150ec (writeSuccessTransactionsAt150ecCallSpec P).
Proof.
  iIntros "#Hlookup Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt150ecCallSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail) "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iAssert (instr_pre 0x10190 (writeSuccessTransactionsAt10190Block P sp base
      transaction transactions processed remaining bytes prefix suffix tail))
    with "[Hnext]" as "HblockNext".
  { iApply (instr_pre_wand 0x10190 0x10190 true true with "Hnext");
      [done | done |].
    iIntros "Hblock".
    rewrite /writeSuccessTransactionsAt10190Spec
      /writeSuccessTransactionsAt10190Block.
    iExists sp, base, transaction, transactions, processed, remaining,
      bytes, prefix, suffix, tail. iFrame. }
  iPoseProof (write_success_transactions_chunk_150ec_jump_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    with "Hlookup HblockNext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt150ecJumpBlock.
  iFrame.
Qed.

Lemma write_success_transactions_at10190_block_unpack
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsAt10190Block P sp base transaction transactions
    processed remaining bytes prefix suffix tail -∗
  reg_col zesu_ram_sys_regs ∗
  "x1" ↦ᵣ RVal_Bits (BV 64 0x150f0) ∗
  writeSuccessTransactionsMachine150e8Rest
    sp base transactions processed transaction ∗
  mmio_range 0x2401a0c0 16 ∗
  spec_trace
    (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 1)
      (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
        (writeSuccessTransactionsEvents sp remaining tail))) ∗
  writeSuccessTransactions150ecCallFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail ∗ True.
Proof.
  rewrite /writeSuccessTransactionsAt10190Block.
  iIntros "Hblock". iExact "Hblock".
Qed.

Global Opaque writeSuccessTransactionsAt10190Block.
