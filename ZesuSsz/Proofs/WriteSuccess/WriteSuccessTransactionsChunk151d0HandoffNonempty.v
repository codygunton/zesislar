Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151d0.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0Defs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0Helpers.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0HandoffInvariant.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0HandoffPost.

Lemma write_success_transactions_151d0_access_handoff_nonempty
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8))
    (tail phase : spec) (P : iProp Sigma)
    (HaccessBounds :
      forall (transaction :
          WriteSuccessTransactionsSpec.writeSuccessTransaction),
        WriteSuccessTransactionsSpec.writeSuccessTransactionValid transaction ->
        ((mapRamBase defaultMap) <= bv_unsigned
           (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessPointer
              transaction))%Z /\
        (bv_unsigned
           (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessPointer
              transaction) +
         Z.of_nat
           (length
             (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessBytes
                transaction)) < (machineRamEnd defaultMap))%Z)
    (entry : writeSuccessAccessEntry) (entries : list writeSuccessAccessEntry)
    (Hentries :
      WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries
        transaction = entry :: entries) :
  (∀ (sp : bv 64) (base : Z)
      (entries : list writeSuccessAccessEntry)
      (bytes : list (bv 8)) (tail : spec) (x19 savedX22 : bv 64),
    instr_body 0x153c0
      (writeSuccessAccessListsLoopExit sp base entries bytes tail x19 savedX22 P)) -∗
  "x22" ↦ᵣ RVal_Bits
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200) -∗
  "x27" ↦ᵣ RVal_Bits
    (bv_zero_extend 64
      (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32)) -∗
  (bv_unsigned sp - 48) ↦ₘ? 152 -∗
  (bv_unsigned sp + 136) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232 -∗
  (bv_unsigned sp + 256) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208 -∗
  (bv_unsigned sp + 264) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 216 -∗
  (bv_unsigned sp + 272) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176 -∗
  (bv_unsigned sp + 1680) ↦ₘ? 64 -∗
  (bv_unsigned sp + 1744) ↦ₘ? 40 -∗
  base ↦ₘ∗ prefix -∗
  (base + 288 * length processed) ↦ₘ∗ suffix -∗
  WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn processed -∗
  WriteSuccessTransactionsSpec.writeSuccessTransactionOwn transaction -∗
  WriteSuccessTransactionsSpec.writeSuccessTransactionsOwn remaining -∗
  mmio_range 604086464 16 -∗
  spec_trace
    (writeSuccessAccessListsEvents sp
      (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries
        transaction) phase) -∗
  P -∗
  WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant sp base
    transactions processed (transaction :: remaining) bytes prefix suffix -∗
  instr_pre
    WriteSuccessTransactionsSpec.writeSuccessTransactionsLoopExitAddress
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsLoopExit
      sp base transactions bytes tail P) -∗
  write_success_transactions_151d0_post sp transaction P.
Proof.
  iStartProof.
  iIntros
    "HexitBody Hx22 Hx27 Hlower Hm136 Hm256 Hm264 Hm272 Hstorage
      HtoScratch Hbase Hsuffix Hprocessed Htransaction Hremaining
      Hmmio Htrace HP Hinv Hexit".
  iPoseProof (write_success_transactions_151d0_invariant_facts
    sp base transactions processed (transaction :: remaining) bytes prefix suffix
      with "Hinv") as "(%HspAlign & %HspLower & %HspUpper)".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionOwn)
    in "Htransaction".
  iDestruct "Htransaction" as
    "(HdataOwn & HaccessOwn & HaccessEntriesOwn & HblobOwn & HauthOwn &
      %Hvalid & _)".
  have HaccessPointer :
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208 =
      WriteSuccessTransactionsSpec.writeSuccessTransactionAccessPointer transaction.
  { unfold WriteSuccessTransactionsSpec.writeSuccessTransactionValid in Hvalid.
    naive_solver. }
  have HaccessCount :
      bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 216) =
      Z.of_nat
        (length
          (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries
             transaction)).
  { unfold WriteSuccessTransactionsSpec.writeSuccessTransactionValid in Hvalid.
    naive_solver. }
  have HaccessBytes :
      WriteSuccessTransactionsSpec.writeSuccessTransactionAccessBytes transaction =
      writeSuccessAccessEntriesBytes
        (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries
           transaction).
  { unfold WriteSuccessTransactionsSpec.writeSuccessTransactionValid in Hvalid.
    naive_solver. }
  iPoseProof (write_success_access_entries_own_length
    (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries transaction)
      with "HaccessEntriesOwn") as
    "(%HaccessEntriesLength & HaccessEntriesOwn)".
  iEval (rewrite <- HaccessPointer; rewrite HaccessBytes) in "HaccessOwn".
  rewrite Hentries in HaccessCount, HaccessBytes, HaccessEntriesLength.
  iEval (rewrite Hentries) in "HaccessOwn HaccessEntriesOwn Htrace".
  iDestruct "HaccessEntriesOwn" as
      "(HentryOwn & HentriesRest & _)".
    iDestruct "HentryOwn" as
      "(HentryStorage & %HentryValid & _)".
    iAssert (writeSuccessAccessEntriesOwn (entry :: entries))%I
      with "[HentryStorage HentriesRest]" as "HaccessEntriesOwnRestore".
    { iEval (cbn [writeSuccessAccessEntriesOwn]).
      iFrame. done. }
    destruct (writeSuccessAccessEntryBytes entry) as
      [|entryByte entryBytes] eqn:HentryBytes.
    { exfalso.
      unfold writeSuccessAccessEntryValid in HentryValid.
      destruct HentryValid as (HentryLength & _).
      rewrite HentryBytes in HentryLength.
      cbn in HentryLength.
      lia. }
    iEval (unfold WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn)
      in "HaccessOwn".
    iEval (cbn) in "HaccessOwn".
    iEval (rewrite HentryBytes) in "HaccessOwn".
    iEval (cbn) in "HaccessOwn".
    iDestruct "HaccessOwn" as
      "(HaccessArray & %HaccessLower & %HaccessUpper & _)".
    iDestruct (mem_mapsto_uninit_split 32 with "Hlower") as
      "[Hlower32 HlowerRest]"; [lia|].
    have HlowerAddress :
        (bv_unsigned sp - 48 + 32 = bv_unsigned sp - 16)%Z by lia.
    iEval (rewrite HlowerAddress) in "HlowerRest".
    iDestruct (mem_mapsto_uninit_split 16 with "HlowerRest") as
      "[Hstack16 HlowerRest]"; [lia|].
    iAssert (writeSuccessStorageKeysScratch sp)%I
      with "[Hstorage]" as "HstorageScratch".
    { iApply (write_success_transactions_151d0_storage_scratch sp).
      iExact "Hstorage". }
    have HentriesBound :
        (length (entry :: entries) < 2 ^ 64)%nat.
    {
      have Hrange := bv_unsigned_in_range 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
          transaction 216).
      rewrite HaccessCount in Hrange.
      unfold bv_modulus in Hrange.
      cbn in Hrange.
      apply (proj2 (Nat2Z.inj_lt _ _)).
      rewrite Nat2Z.inj_pow.
      exact (proj2 Hrange).
    }
    have HaccessUpperFull :
        bv_unsigned
          (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
            transaction 208) +
        Z.of_nat
          (length (writeSuccessAccessEntriesBytes (entry :: entries))) <
        (machineRamEnd defaultMap).
    { cbn [writeSuccessAccessEntriesBytes].
      rewrite HentryBytes. cbn. exact HaccessUpper. }
    iPoseProof (write_success_transactions_151d0_nonempty_invariant
      sp
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208))
      entry entries HaccessEntriesLength HentriesBound HspAlign HspLower HspUpper
      HaccessLower HaccessUpperFull) as "HaccessInvariant".
    iAssert (instr_pre 0x153c0
      (writeSuccessAccessListsLoopExit sp
        (bv_unsigned
          (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208))
        (entry :: entries)
        (writeSuccessAccessEntriesBytes (entry :: entries))
        (phase)
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224)
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232) P))%I
      with "[HexitBody]" as "HexitAccess".
    {
      iApply (instr_pre_wand 0x153c0 0x153c0 false true with "HexitBody");
        [done | done |].
      iIntros "$".
    }
    iDestruct (mem_mapsto_array_app 8%N
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208))
      (DfracOwn 1) ([] : list (bv 8))
      (writeSuccessAccessEntriesBytes (entry :: entries))
      with "[HaccessArray]") as
      "[HemptyAccess HaccessArray]".
    { cbn [writeSuccessAccessEntriesBytes].
      rewrite HentryBytes. cbn. iExact "HaccessArray". }
  iEval (cbn; rewrite Z.add_0_r) in "HaccessArray".
  iApply (write_success_transactions_151d0_nonempty_post
    sp transaction phase P entry entries HaccessCount with
    "Hx22 Hx27 HemptyAccess HaccessArray HaccessEntriesOwnRestore
      Hm136 Hm256 Hm264 Hm272 HtoScratch Hstack16 HstorageScratch
      Hmmio Htrace HP HaccessInvariant HexitAccess").
  Unshelve.
  all: try done.
Qed.
