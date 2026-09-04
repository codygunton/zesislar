From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsBoundary15210.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsBoundary1521c.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Remove Hints writeSuccessAccessEntryStorageOwn_unfold :
  typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_access_lists_chunk_15210
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x1521c (writeSuccessAccessListsAt1521cSpec x19 P) -∗
  instr_body 0x15210 (writeSuccessAccessListsAt15210Spec x19 P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hint Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  run_write_success_access_lists_chunk 0x1521c.
  Unshelve. all: try run_write_success_access_lists_return 0x1521c.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  pose proof H0 as HentryValid.
  iExists (writeSuccessAccessEntryWord entry 8, tt)ₗ.
  liARun.
  Unshelve.
  iRename select
    ((bv_unsigned sp + 1744) ↦ₘ∗ writeSuccessAccessEntryBytes entry)%I
    into "Hcopied".
  iDestruct (mem_mapsto_array_region 8%N (bv_unsigned sp + 1744)
    (DfracOwn 1) (writeSuccessAccessEntryBytes entry) 8 8
    with "Hcopied") as "(Hprefix & Hword & Hsuffix)".
  { destruct HentryValid as (HentryLength & _).
    rewrite HentryLength. lia. }
  iDestruct (mem_mapsto_byte_array_to_mapsto with "Hword") as "Hword".
  destruct HentryValid as (HentryLength & _).
  have HwordLength :
      length (take 8 (drop 8 (writeSuccessAccessEntryBytes entry))) = 8%nat.
  { rewrite length_take length_drop HentryLength. lia. }
  have HwordAddress :
      (bv_unsigned sp + 1744 + 8 =
       bv_unsigned sp + 1752)%Z by lia.
  have HspAlign8 : (bv_unsigned sp mod 8 = 0)%Z.
  { pose proof H6 as HspAlign16.
    apply Z.mod_divide in HspAlign16; [|lia].
    destruct HspAlign16 as [k Hk].
    apply Z.mod_divide; [lia|].
    exists (2 * k)%Z.
    lia. }
  iEval (rewrite /writeSuccessAccessEntryWord HwordLength /= Z.mul_1_l
    HwordAddress) in "Hword".
  iEval (cbn; rewrite Z.mul_1_l) in "Hsuffix".
  iSplitL "Hword".
  { rewrite /writeSuccessAccessEntryWord. iExact "Hword". }
  iSplit.
  { iPureIntro. now rewrite HspAlign8. }
  iSplit.
  { iPureIntro. lia. }
  iApply instr_pre_to_body.
  iNext.
  liARun.
  iSplit; last done.
  iIntros "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace & _)".
  iRename select
    ((bv_unsigned sp + 1752) ↦ₘ writeSuccessAccessEntryWord entry 8)%I
    into "HwordCurrent".
  iAssert
    ((bv_unsigned sp + 1744) ↦ₘ∗ writeSuccessAccessEntryBytes entry)%I
    with "[Hprefix Hsuffix HwordCurrent]" as "Hcopied".
  { iApply (mem_mapsto_array_recombine_u64_read
      (bv_unsigned sp + 1744) (writeSuccessAccessEntryBytes entry) 8
      (bv_unsigned sp + 1744 + 16) (bv_unsigned sp + 1752)
      with "Hprefix Hsuffix HwordCurrent").
    - iPureIntro. reflexivity.
    - iPureIntro.
      cbn. lia.
    - iPureIntro. rewrite HentryLength. lia. }
  iExists sp.
  iExists base.
  iExists entry.
  iExists (processed ++ entry :: remaining).
  iExists processed.
  iExists remaining.
  iExists
    (writeSuccessAccessEntriesBytes (processed ++ entry :: remaining)).
  iExists (writeSuccessAccessEntriesBytes processed).
  iExists
    (writeSuccessAccessEntryBytes entry ++
     writeSuccessAccessEntriesBytes remaining).
  iExists savedX22.
  iExists ((sp - BV 64 16)%bv).
  iExists (BV 64 8).
  iExists x22.
  iExists x27.
  iExists tail.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.
