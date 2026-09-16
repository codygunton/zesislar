Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151d0.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0Defs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0Helpers.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0Handoff.

Lemma write_success_transactions_chunk_151d0
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  (∀ (sp : bv 64) (base : Z)
      (entries : list writeSuccessAccessEntry)
      (bytes : list (bv 8)) (tail : spec) (x19 savedX22 : bv 64),
    instr_body 0x153c0
      (writeSuccessAccessListsLoopExit sp base entries bytes tail x19 savedX22 P)) -∗
  ⌜(∀ (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction),
    WriteSuccessTransactionsSpec.writeSuccessTransactionValid transaction ->
    ((mapRamBase defaultMap) <=
       bv_unsigned
         (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessPointer
            transaction))%Z /\
    (bv_unsigned
       (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessPointer
          transaction) +
       Z.of_nat
       (length
           (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessBytes
              transaction)) < (machineRamEnd defaultMap))%Z)⌝ -∗
  (∀ x19, instr_body 0x151d4 (writeSuccessAccessListsLoopSpec x19 P)) -∗
  instr_body 0x151d0 (writeSuccessTransactionsAt151d0Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode HexitBody %HaccessBounds Hnext".
  iAssert (write_success_transactions_151d0_next P)%I
    with "[Hnext]" as "HnextWrapped".
  { iEval (unfold write_success_transactions_151d0_next); iExact "Hnext". }
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
  Unshelve.
  iIntros "Hto _ _ Hhandoff HPC".
  iDestruct "Hhandoff" as
    "(Hbase & Hsuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & Hinv & Hexit & _)".
  iEval (unfold write_success_transactions_151d0_next) in "HnextWrapped".
  iRename "HnextWrapped" into "Hnext".
  iPoseProof (write_success_transactions_151d0_invariant_facts
    sp base transactions processed (transaction :: remaining) bytes prefix suffix
      with "Hinv")
    as "(%HspAlign & %HspLower & %HspUpper)".
  have HspAlign8 : (bv_unsigned sp `mod` 8 = 0)%Z.
  {
    have Hneq8 : (8 : Z) <> 0%Z by lia.
    apply (proj2 (Z.mod_divide (bv_unsigned sp) 8 Hneq8)).
    have Hdiv16 : (16 | bv_unsigned sp)%Z.
    {
      have Hneq16 : (16 : Z) <> 0%Z by lia.
      apply (proj1 (Z.mod_divide (bv_unsigned sp) 16 Hneq16)).
      exact HspAlign.
    }
    destruct Hdiv16 as [factor Hfactor].
    exists (2 * factor)%Z.
    rewrite Hfactor.
    ring.
  }
  iSpecialize ("Hnext" $!
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224)).
  iPoseProof "Hnext" as "HnextCopy".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  iAssert ((bv_unsigned sp + 1744) ↦ₘ? 40)%I
    with "[Hto]" as "HtoScratch".
  { iApply (write_success_transactions_151d0_to_scratch sp transaction).
    iExact "Hto". }
  iRename select
    ("x22" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200))%I
    into "Hx22".
  iRename select
    ("x27" ↦ᵣ RVal_Bits
      (bv_zero_extend 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32)))%I
    into "Hx27".
  iRename select ((bv_unsigned sp - 48) ↦ₘ? 152)%I into "Hlower".
  iRename select
    ((bv_unsigned sp + 136) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232)%I
    into "Hm136".
  iRename select
    ((bv_unsigned sp + 256) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208)%I
    into "Hm256".
  iRename select
    ((bv_unsigned sp + 264) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 216)%I
    into "Hm264".
  iRename select
    ((bv_unsigned sp + 272) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176)%I
    into "Hm272".
  iRename select ((bv_unsigned sp + 1680) ↦ₘ? 64)%I into "Hstorage".
  iPoseProof
    (write_success_transactions_151d0_access_handoff
      sp base transaction transactions processed remaining bytes prefix suffix
      tail (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
          WriteSuccessTransactionsSpec.TransactionBlobCount sp transaction
          (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
            sp remaining tail)) P HaccessBounds
      with "HexitBody Hx22 Hx27 Hlower Hm136 Hm256 Hm264
        Hm272 Hstorage HtoScratch Hbase Hsuffix Hprocessed Htransaction
        Hremaining Hmmio Htrace HP Hinv Hexit") as "Hpost".
  iEval (unfold write_success_transactions_151d0_post) in "Hpost".
  iDestruct "Hpost" as
    (phase x27 x22 savedX22 storedIndex suffixBytes prefixBytes accessBytes
      accessProcessed accessRemaining accessEntries accessBase)
    "(%Hzero & Hx22Post & Hx27Post & HprefixPost & HsuffixPost &
      HremainingPost & HprocessedPost & HscratchPost & HmmioPost &
      HtracePost & HPPost & HinvPost & HexitPost & _)".
  iExists (phase, x27, x22, savedX22, storedIndex, suffixBytes, prefixBytes,
    accessBytes, accessProcessed, accessRemaining, accessEntries, accessBase, tt)ₗ.
  cbn.
  iSplit; [iPureIntro; exact Hzero|].
  iFrame.

  Unshelve.
  all: try done.
Qed.
