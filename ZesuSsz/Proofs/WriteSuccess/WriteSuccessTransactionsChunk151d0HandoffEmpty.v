Require Import ZesuSsz.Automation.All.
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

Lemma write_success_transactions_151d0_access_handoff_empty
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
    (Hentries :
      WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries
        transaction = []) :
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
  iEval (unfold write_success_transactions_151d0_post).
  iExists phase,
      (bv_zero_extend 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32)),
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200),
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232),
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176),
      (writeSuccessAccessEntriesBytes ([] : list writeSuccessAccessEntry)), [],
      (writeSuccessAccessEntriesBytes ([] : list writeSuccessAccessEntry)),
      ([] : list writeSuccessAccessEntry), [], ([] : list writeSuccessAccessEntry),
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208)).
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
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn)
      in "HaccessOwn".
    iEval (cbn) in "HaccessOwn".
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
    pose proof (HaccessBounds transaction Hvalid) as
      (HaccessLower & HaccessUpper).
    rewrite <- HaccessPointer in HaccessLower, HaccessUpper.
    rewrite HaccessBytes in HaccessUpper.
    cbn in HaccessUpper.
    iAssert (writeSuccessAccessListsInvariant sp
        (bv_unsigned
          (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208))
      [] [] [] (writeSuccessAccessEntriesBytes []) []
      (writeSuccessAccessEntriesBytes []))%I
      with "[]" as "HaccessInvariant".
    {
      rewrite /writeSuccessAccessListsInvariant.
      iSplit; [iPureIntro; reflexivity|].
      iSplit; [iPureIntro; cbn; reflexivity|].
      iSplit; [iPureIntro; cbn; reflexivity|].
      iSplit; [iPureIntro; cbn; reflexivity|].
      iSplit; [iPureIntro; cbn; reflexivity|].
      iSplit; [iPureIntro; cbn; lia|].
      iSplit; [iPureIntro; cbn; lia|].
      iSplit; [iPureIntro; cbn; lia|].
      iSplit; [iPureIntro; cbn; lia|].
      iSplit; [iPureIntro; exact HspAlign|].
      iSplit; [iPureIntro; lia|].
      iSplit; [iPureIntro; exact HspUpper|].
      iSplit; [iPureIntro; intros _; exact HaccessLower|].
      iSplit; [iPureIntro; intros _; exact HaccessUpper|].
      done.
    }
    iAssert (instr_pre 0x153c0
      (writeSuccessAccessListsLoopExit sp
        (bv_unsigned
          (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208))
        [] (writeSuccessAccessEntriesBytes [])
        (phase)
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224)
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232) P))%I
      with "[HexitBody]" as "HexitAccess".
    {
      iApply (instr_pre_wand 0x153c0 0x153c0 false true with "HexitBody");
        [done | done |].
      iIntros "$".
    }
    have Hm256Eq :
        Z_to_bv 64
          (bv_unsigned
            (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
              transaction 208)) =
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208.
    { bv_solve. }
    have Hm264Eq :
        Z_to_bv 64 (Z.of_nat (length ([] : list writeSuccessAccessEntry))) =
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 216.
    { apply bv_eq.
      rewrite Z_to_bv_unsigned HaccessCount; reflexivity. }
    iEval (rewrite <- Hm256Eq) in "Hm256".
    iEval (rewrite <- Hm264Eq) in "Hm264".
    iFrame "HtoScratch Hstack16 HstorageScratch HaccessInvariant HexitAccess".
    iFrame.
    iSplit; [iPureIntro; bv_solve|].
    iEval (cbn; rewrite Z.add_0_r).
    iAssert
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208)
        ↦ₘ∗ ([] : list (bv 8)))%I
      with "[]" as "HemptyBytes".
    {
      iApply (write_success_transactions_151d0_empty_array).
      pose proof (bv_unsigned_in_range 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
          transaction 208)) as Hrange.
      unfold bv_modulus in Hrange.
      cbn in Hrange.
      iPureIntro; lia.
    }
    iAssert
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208)
        ↦ₘ∗ ([] : list (bv 8)))%I
      with "[]" as "HemptyBytes2".
    {
      iApply (write_success_transactions_151d0_empty_array).
      pose proof (bv_unsigned_in_range 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
          transaction 208)) as Hrange.
      unfold bv_modulus in Hrange.
      cbn in Hrange.
      iPureIntro; lia.
    }
    iFrame "HemptyBytes HemptyBytes2".
  Unshelve.
  all: try done.
Qed.
