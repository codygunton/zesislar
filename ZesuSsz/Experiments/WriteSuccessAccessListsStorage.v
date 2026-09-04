From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysLoop.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsChunk1521c.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsBoundary1521c.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsBoundary15224.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsStorageFrame.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsStorageNonzero.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_access_lists_storage_any_loop_pre
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15228
    (writeSuccessAccessListsStorageAnyLoopSpec x19 P).
Proof.
  iIntros "#Hlookup #Hcode #Houtput".
  iAssert (□ ∀ (sp : bv 64) (storageBase : Z) (total : nat)
      (storageBytes : list (bv 8)) (storageTail : spec),
      instr_pre 0x15228
        (writeSuccessStorageKeysLoopSpec x19
          (writeSuccessAccessListsStorageFrame
            x19 P sp storageBase total storageBytes storageTail)))%I
    as "#HallLoops".
  { iModIntro. iIntros (sp storageBase total storageBytes storageTail).
    iApply (write_success_storage_keys_loop_pre x19
      (writeSuccessAccessListsStorageFrame
        x19 P sp storageBase total storageBytes storageTail) with
      "Hlookup Hcode Houtput"). }
  rewrite instr_pre'_eq.
  iModIntro. iNext.
  iIntros "(%sp & %storageBase & %total & %storageBytes & %storageTail &
    HloopSpec)".
  iSpecialize ("HallLoops" $! sp storageBase total storageBytes storageTail).
  iPoseProof "HallLoops" as "#Hloop".
  iDestruct ("Hloop" with "HloopSpec") as (instruction) "(Hinstr & Hwp)".
  iExists instruction. iFrame.
Qed.

Definition writeSuccessAccessListsTailPayload
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma)
    (sp : bv 64) : iProp Sigma :=
  (∃ (base : Z) (entry : writeSuccessAccessEntry)
      (entries processed remaining : list writeSuccessAccessEntry)
      (bytes prefix suffix : list (bv 8)) (savedX22 : bv 64) (tail : spec),
    base ↦ₘ∗ prefix ∗
    (base + 40 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
    writeSuccessAccessEntriesOwn processed ∗
    writeSuccessAccessEntriesOwn (entry :: remaining) ∗
    writeSuccessAccessListsScratch sp base (length entries)
      (Z_to_bv 64 (Z.of_nat (length processed))) savedX22 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessAccessListsEvents sp remaining tail) ∗ P ∗
    writeSuccessAccessListsInvariant sp base entries processed
      (entry :: remaining) bytes prefix suffix ∗
    instr_pre 0x153c0
      (writeSuccessAccessListsLoopExit
        sp base entries bytes tail x19 savedX22 P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAccessListsTailPayload) := I.

Lemma write_success_access_lists_zero_storage_to_tail
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma)
    (sp : bv 64) (base : Z) (entry : writeSuccessAccessEntry)
    (entries processed remaining : list writeSuccessAccessEntry)
    (bytes prefix suffix : list (bv 8)) (savedX22 : bv 64) (tail : spec)
    (Hzero : writeSuccessAccessEntryWord entry 8 = BV 64 0) :
  (base ↦ₘ∗ prefix ∗
   (base + 40 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessAccessEntriesOwn processed ∗
   writeSuccessAccessEntryStorageOwn entry ∗
   ⌜writeSuccessAccessEntryValid entry⌝ ∗
   writeSuccessAccessEntriesOwn remaining ∗
   writeSuccessAccessListsCopiedScratch
     sp base (length entries) (length processed) entry savedX22 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeSuccessStorageKeysEvents sp
       (writeSuccessAccessEntryStorageCount entry)
       (writeSuccessAccessListsEvents sp remaining tail)) ∗ P ∗
   writeSuccessAccessListsInvariant sp base entries processed
     (entry :: remaining) bytes prefix suffix ∗
   instr_pre 0x153c0
     (writeSuccessAccessListsLoopExit
       sp base entries bytes tail x19 savedX22 P) ∗ True) -∗
  writeSuccessAccessListsTailPayload x19 P sp.
Proof.
  iIntros "(Hprefix & Hsuffix & Hprocessed & HentryStorage & %Hvalid &
    Hremaining & Hcopied & Hmmio & Htrace & HP & Hinv & Hexit & _)".
  destruct Hvalid as
    [HentryLength [Hpointer [Hcount [HstorageLength HcountBound]]]].
  have HcountZero : writeSuccessAccessEntryStorageCount entry = O.
  { destruct (writeSuccessAccessEntryStorageCount entry) as [|count]
    eqn:HcountCase; first done.
    rewrite Hcount in Hzero.
    have HzeroUnsigned := f_equal bv_unsigned Hzero.
    rewrite Z_to_bv_unsigned in HzeroUnsigned.
    have HcountBoundZ :=
      (proj1 (Nat2Z.inj_lt (S count) (2 ^ 64))) HcountBound.
    rewrite Nat2Z.inj_pow in HcountBoundZ.
    have Hrange :
        0 <= Z.of_nat (S count) < bv_modulus 64.
    { unfold bv_modulus. cbn. lia. }
    rewrite (bv_wrap_small 64 _ Hrange) in HzeroUnsigned.
    rewrite bv_unsigned_BV in HzeroUnsigned.
    cbn in HzeroUnsigned. lia. }
  iAssert (writeSuccessAccessEntryOwn entry)%I
    with "[HentryStorage]" as "HentryOwn".
  { rewrite /writeSuccessAccessEntryOwn /writeSuccessAccessEntryStorageOwn
      HcountZero.
    iFrame. iPureIntro. repeat split; assumption. }
  iDestruct "Hcopied" as
    "(Hsaved & Hbase & Htotal & Hindex & Hcopied & Houtput & Hstorage & _)".
  iPoseProof (write_success_byte_array_to_uninit
    (bv_unsigned sp + 1744) (writeSuccessAccessEntryBytes entry)
    with "Hcopied") as "Hcopied".
  iEval (rewrite HentryLength) in "Hcopied".
  iAssert (writeSuccessAccessListsScratch sp base (length entries)
      (Z_to_bv 64 (Z.of_nat (length processed))) savedX22)%I
    with "[Hsaved Hbase Htotal Hindex Hcopied Houtput Hstorage]" as
    "Hscratch".
  { rewrite /writeSuccessAccessListsScratch.
    iFrame. }
  iEval (rewrite HcountZero /=) in "Htrace".
  iExists base, entry, entries, processed, remaining, bytes,
    prefix, suffix, savedX22, tail.
  iFrame.
Qed.

Lemma write_success_access_lists_chunk_15224
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x153b4 (writeSuccessAccessListsTailSpec x19 P) -∗
  instr_body 0x15224 (writeSuccessAccessListsAt15224Spec x19 P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  iPoseProof (write_success_access_lists_storage_any_loop_pre x19 P with
    "Hlookup Hcode Houtput") as "#Hstorage".
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
  all: iIntros "HentryStorage".
  all: iIntros "HentryValid".
  all: iIntros "Hremaining".
  all: iIntros "Hstate".
  all: iIntros "HPC".
  all: liARun.
  Unshelve.
  - iDestruct "HentryValid" as "[HentryValid _]".
    iDestruct "Hremaining" as "[Hremaining _]".
    iPoseProof (write_success_access_lists_zero_storage_to_tail
      x19 P sp base entry entries processed remaining bytes prefix suffix
      savedX22 tail H1 with "[-]") as "Hpayload".
    { iFrame. }
    iDestruct "Hpayload" as
      (payloadBase payloadEntry payloadEntries payloadProcessed
        payloadRemaining payloadBytes payloadPrefix payloadSuffix
        payloadSavedX22 payloadTail)
      "Hpayload".
    iExists (payloadTail, payloadSavedX22, payloadSuffix, payloadPrefix, payloadBytes,
      payloadRemaining, payloadProcessed, payloadEntries, payloadEntry,
      payloadBase, tt)ₗ.
    iExact "Hpayload".
  - iDestruct "HentryValid" as "[HentryValid _]".
    iDestruct "Hremaining" as "[Hremaining _]".
    iDestruct "Hstate" as
      "(Hcopied & Hmmio & Htrace & HP & #Hinv & Hexit & _)".
    iPoseProof (write_success_access_lists_nonzero_storage_to_loop
      x19 P sp base entry entries processed remaining bytes prefix suffix
      savedX22 x10 x11 tail H1 with "[$]") as "Hloop".
    iDestruct "Hloop" as
      (loopSp loopBase loopTotal loopBytes loopTail) "Hloop".
    iExists (loopTail, loopBytes, loopTotal, loopBase, loopSp, tt)ₗ.
    iExact "Hloop".
  - prepare_sidecond. bv_solve.
Qed.

Lemma write_success_access_lists_storage
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x153b4 (writeSuccessAccessListsTailSpec x19 P) -∗
  instr_body 0x1521c (writeSuccessAccessListsAt1521cSpec x19 P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Houtput Hnext".
  iApply (write_success_access_lists_chunk_1521c x19 P with
    "Hlookup Hcode").
  iApply (write_success_access_lists_chunk_15224 x19 P with
    "Hlookup Hcode Houtput Hnext").
Qed.
