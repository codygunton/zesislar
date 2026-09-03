From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsBoundary1521c.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsBoundary15224.

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

Ltac liAStepToNil :=
  lazymatch goal with
  | |- context[WPasm ?trace] =>
      let trace' := (eval cbv [TRACE_LET] in trace) in
      lazymatch trace' with
      | tnil => idtac
      | _ => liAStep; liAStepToNil
      end
  | |- context[WPasm] => liAStep; liAStepToNil
  | _ => first [liAStep; liAStepToNil | shelve]
  end.

Lemma write_success_access_lists_chunk_1521c
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15224 (writeSuccessAccessListsAt15224Spec x19 P) -∗
  instr_body 0x1521c (writeSuccessAccessListsAt1521cSpec x19 P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  rewrite instr_pre'_eq.
  iIntros "Hout".
  iEval (unfold writeSuccessAccessListsAt1521cSpec,
    writeSuccessAccessListsCopiedSpec) in "Hout".
  iDestruct "Hout" as
    (sp base entry entries processed remaining bytes prefix suffix
      x10 x11 x22 x27 tail)
    "(Hsys & Hother & Hx2 & Hx10 & Hx19 & Hx11 & Hx22 & Hx27 &
      HbasePrefix & HbaseSuffix & HprocessedOwn & HentryOwn & Hscratch &
      Hmmio & Htrace & HP & Hinv & Hloop & _)".
  iEval (unfold writeSuccessAccessEntriesOwn) in "HentryOwn".
  iDestruct "HentryOwn" as "(HentryOwn & HremainingOwn & _)".
  iDestruct "HentryOwn" as "(HstorageOwn & %HentryValid & _)".
  iAssert (writeSuccessAccessEntryOwn entry)%I with "[HstorageOwn]"
    as "HentryOwn".
  { iEval (unfold writeSuccessAccessEntryOwn); iFrame; done. }
  iAssert (writeSuccessAccessEntriesOwn (entry :: remaining))%I
    with "[HentryOwn HremainingOwn]" as "HentryOwnList".
  { iEval (unfold writeSuccessAccessEntriesOwn); iFrame; done. }
  iAssert (writeSuccessAccessListsAt1521cSpec x19 P)%I
    with "[Hsys Hother Hx2 Hx10 Hx19 Hx11 Hx22 Hx27 HbasePrefix
      HbaseSuffix HprocessedOwn HentryOwnList Hscratch Hmmio Htrace HP
      Hinv Hloop]" as "Hout".
  { iEval (unfold writeSuccessAccessListsAt1521cSpec,
      writeSuccessAccessListsCopiedSpec); iFrame; done. }
  run_write_success_access_lists_chunk 0x15224.
  Unshelve. all: try run_write_success_access_lists_return 0x15224.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try (rewrite !Z.sub_diag; cbn;
    destruct H0 as (HentryLength & _);
    rewrite HentryLength; lia).
  all: try (rewrite !Z.sub_diag;
    replace (Z.to_nat 0) with 0%nat by reflexivity;
    cbn;
    assert (Hzero :
      (bv_unsigned sp + 1752 - (bv_unsigned sp + 1744 + 8))%Z = 0)
      by lia;
    rewrite Hzero;
    cbn).
  all: try (destruct H0 as (HentryLength & _);
    rewrite length_drop HentryLength; cbn; lia).
  Unshelve.
  iExists (Some IslaTraces.write_success_57.a1521c.a1521c, tt)ₗ.
  liARun.
  iSplit.
  - iEval (rewrite /InstrSpecs.Lookup.instr_lookup_resources) in "Hlookup".
    iPoseProof ("Hlookup" $! 0x1521c with "[//]") as "Hinstr".
    iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a1521c)
      in "Hinstr".
    iExact "Hinstr".
  - iIntros "HPC".
    iEval (unfold writeSuccessAccessListsAt1521cSpec,
      writeSuccessAccessListsCopiedSpec) in "Hout".
    iDestruct "Hout" as
      (sp2 base2 entry2 entries2 processed2 remaining2 bytes2 prefix2 suffix2
        x10_2 x11_2 x22_2 x27_2 tail2)
      "(Hsys & Hother & Hx2 & Hx10 & Hx19 & Hx11 & Hx22 & Hx27 &
        HbasePrefix & HbaseSuffix & HprocessedOwn & HentryOwn & Hscratch &
        Hmmio & Htrace & HP & Hinv & Hloop & _)".
    iDestruct "Hinv" as
      "(%HentriesEq2 & %HbytesEq2 & %HprefixEq2 & %HsuffixEq2 &
        HbytesConcatRest & HbytesLenRest & HprefixLenRest & HsuffixLenRest &
        HentriesLenRest & HspAlignRest & HspLowerRest & HspUpperRest &
        HbaseLowerRest & HbaseUpperRest & _)".
    iDestruct "HspLowerRest" as "%HspLower2".
    iDestruct "HspUpperRest" as "%HspUpper2".
    iDestruct "HspAlignRest" as "%HspAlign2".
    have Haddress :
        bv_unsigned (sp2 + BV 64 1744) = (bv_unsigned sp2 + 1744)%Z
      by bv_solve.
    iEval (unfold writeSuccessAccessEntriesOwn) in "HentryOwn".
    iDestruct "HentryOwn" as "(HentryOwn2 & HremainingOwn2 & _)".
    iDestruct "HentryOwn2" as "(HstorageOwn2 & %HentryValid2 & _)".
    iEval (unfold writeSuccessAccessListsCopiedScratch) in "Hscratch".
    iDestruct "Hscratch" as
      (savedX22)
      "(HsavedX22 & HbasePtr & Htotal & Hprocessed & Hcopied &
        HscratchStack & HstorageScratch & _)".
    have HentryLength :
        length (writeSuccessAccessEntryBytes entry2) = 40%nat
      by exact (proj1 HentryValid2).
    have HwordLength :
        length (take 8 (drop 0 (writeSuccessAccessEntryBytes entry2))) = 8%nat.
    { rewrite drop_0 length_take HentryLength. lia. }
    iDestruct (mem_mapsto_array_region 8%N (bv_unsigned sp2 + 1744)
      (DfracOwn 1) (writeSuccessAccessEntryBytes entry2) 0 8
      with "Hcopied") as "(Hprefix & HwordBytes & Hsuffix)".
    { rewrite HentryLength. lia. }
    iDestruct (mem_mapsto_byte_array_to_mapsto with "HwordBytes") as "Hword".
    iEval (rewrite HwordLength /writeSuccessAccessEntryWord /= Z.mul_1_l
      Z.add_0_r)
      in "Hword".
    iAssert
      ((bv_unsigned (sp2 + BV 64 1744)) ↦ₘ
        writeSuccessAccessEntryWord entry2 0)%I
      with "[Hword]" as "HwordNormalized".
    { rewrite Haddress. iExact "Hword". }
    iEval (cbn; rewrite Z.mul_1_l) in "Hsuffix".
    have HwordLength2 :
        length (take 8 (drop 0
          (drop 8 (writeSuccessAccessEntryBytes entry2)))) = 8%nat.
    { rewrite drop_0 length_take length_drop HentryLength. lia. }
    have HwordAddress2 :
        (bv_unsigned sp2 + 1744 + 8 = bv_unsigned sp2 + 1752)%Z by lia.
    iDestruct (mem_mapsto_array_region 8%N (bv_unsigned sp2 + 1744 + 8)
      (DfracOwn 1) (drop 8 (writeSuccessAccessEntryBytes entry2)) 0 8
      with "Hsuffix") as "(Hprefix2 & HwordBytes2 & Hsuffix2)".
    { rewrite length_drop HentryLength. lia. }
    iDestruct (mem_mapsto_byte_array_to_mapsto with "HwordBytes2")
      as "Hword2".
    iEval (rewrite HwordLength2 /writeSuccessAccessEntryWord /=
      Z.mul_1_l Z.add_0_r drop_0) in "Hword2".
    iEval (rewrite HwordAddress2) in "Hword2".
    iEval (rewrite /InstrSpecs.Lookup.instr_lookup_resources) in "Hlookup".
    iPoseProof ("Hlookup" $! 0x15220 with "[//]") as "Hinstr20".
    iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a15220)
      in "Hinstr20".
    iEval (unfold IslaTraces.write_success_57.a1521c.a1521c).
    liAStepToNil.
    li_unfold_lets_in_context; simpl; try liToSyntaxGoal.
    iRename select ("PC" ↦ᵣ _)%I into "HPC20".
    unLET.
    have HPC20Value :
        (Z_to_bv 64 86556 + 4)%bv = Z_to_bv 64 86560 by bv_solve.
    iEval (rewrite HPC20Value) in "HPC20".
    have HPC20Address :
        bv_unsigned (Z_to_bv 64 86560) = 86560 by bv_solve.
    iEval (rewrite <- HPC20Address) in "Hinstr20".
    iApply
      (wp_next_instr (Z_to_bv 64 86560)
        IslaTraces.write_success_57.a15220.a15220
        with "[$] Hinstr20").
    iNext.
    iIntros "HPCnext".
    iEval (unfold IslaTraces.write_success_57.a15220.a15220).
    liAStepToNil.
    li_unfold_lets_in_context; simpl; try liToSyntaxGoal.
    iRename select ("PC" ↦ᵣ _)%I into "HPC24".
    unLET.
    have HPC24Value :
        (Z_to_bv 64 86560 + 4)%bv = Z_to_bv 64 86564 by bv_solve.
    iEval (rewrite HPC24Value) in "HPC24".
    have HPC24Address :
        bv_unsigned (Z_to_bv 64 86564) = 86564 by bv_solve.
    iRename select
      ((bv_unsigned (sp2 + BV 64 1744)) ↦ₘ _)%I into "HwordCurrent0".
    iRename select ("x22" ↦ᵣ _)%I into "Hx22Current".
    iRename select ("x2" ↦ᵣ _)%I into "Hx2Current".
    iRename select (reg_col zesu_ram_sys_regs)%I into "HsysCurrent".
    iRename select
      ((bv_unsigned (sp2 + BV 64 1752)) ↦ₘ _)%I into "HwordCurrent8".
    iRename select ("x27" ↦ᵣ _)%I into "Hx27Current".
    iEval (rewrite Haddress) in "HwordCurrent0".
    have HaddressWord8 :
        bv_unsigned (sp2 + BV 64 1752) = (bv_unsigned sp2 + 1752)%Z
      by bv_solve.
    iEval (rewrite HaddressWord8) in "HwordCurrent8".
    iEval (rewrite -instr_pre'_eq) in "Hnext".
    iAssert
      ((bv_unsigned sp2 + 1744 + 8) ↦ₘ∗
        drop 8 (writeSuccessAccessEntryBytes entry2))%I
      with "[Hprefix2 Hsuffix2 HwordCurrent8]" as "Hsecond".
    { iApply (mem_mapsto_array_recombine_u64_read
        (bv_unsigned sp2 + 1744 + 8)
        (drop 8 (writeSuccessAccessEntryBytes entry2)) 0
        (bv_unsigned sp2 + 1744 + 8 + 1 * 8%nat)
        (bv_unsigned sp2 + 1752)
        with "Hprefix2 Hsuffix2 HwordCurrent8").
      - iPureIntro. reflexivity.
      - iPureIntro. rewrite HwordAddress2. cbn. lia.
      - iPureIntro. rewrite length_drop HentryLength. lia. }
    iAssert
      ((bv_unsigned sp2 + 1744) ↦ₘ∗
        writeSuccessAccessEntryBytes entry2)%I
      with "[Hprefix Hsecond HwordCurrent0]" as "HcopiedFinal".
    { iApply (mem_mapsto_array_recombine_u64_read
        (bv_unsigned sp2 + 1744)
        (writeSuccessAccessEntryBytes entry2) 0
        (bv_unsigned sp2 + 1744 + 8) (bv_unsigned sp2 + 1744)
        with "Hprefix Hsecond HwordCurrent0").
      - iPureIntro. reflexivity.
      - iPureIntro. cbn. lia.
      - iPureIntro. rewrite HentryLength. lia. }
    have Hx22Value :
        bv_sign_extend 64 (writeSuccessAccessEntryWord entry2 0) =
          writeSuccessAccessEntryWord entry2 0 by rewrite bv_sign_extend_idemp.
    iEval (rewrite Hx22Value) in "Hx22Current".
    have Hx27Value :
        bv_sign_extend 64
          (Z_to_bv (8 * 8)
            (little_endian_to_bv 8
              (take 8 (drop 8 (writeSuccessAccessEntryBytes entry2))))) =
          writeSuccessAccessEntryWord entry2 8.
    { rewrite /writeSuccessAccessEntryWord. bv_solve. }
    iEval (rewrite Hx27Value) in "Hx27Current".
    let spT := constr:(sp2) in
    let baseT := constr:(base2) in
    let entryT := constr:(entry2) in
    let processedT := constr:(processed2) in
    let remainingT := constr:(remaining2) in
    let entriesT := constr:(processed2 ++ entry2 :: remaining2) in
    let bytesT :=
      constr:(writeSuccessAccessEntriesBytes
        (processed2 ++ entry2 :: remaining2)) in
    let prefixT := constr:(writeSuccessAccessEntriesBytes processed2) in
    let suffixT :=
      constr:(writeSuccessAccessEntriesBytes (entry2 :: remaining2)) in
    let x10T := constr:(x10_2) in
    let x11T := constr:(x11_2) in
    let tailT := constr:(tail2) in
    let HentryValidT := constr:(HentryValid2) in
    iApply
      (wp_next_instr_pre (Z_to_bv 64 86564)
        (writeSuccessAccessListsAt15224Spec x19 P) false
        with "[$] [Hnext]");
    [ rewrite HPC24Address; iExact "Hnext"
    | rewrite /writeSuccessAccessListsAt15224Spec;
      iExists spT, baseT, entryT, entriesT, processedT, remainingT,
        bytesT, prefixT, suffixT, x10T, x11T, tailT;
      iAssert (writeSuccessAccessEntryOwn entryT)%I
        with "[HstorageOwn2]" as "HentryTarget";
      [ iEval (unfold writeSuccessAccessEntryOwn);
        iSplit; [iExact "HstorageOwn2" | idtac];
        iSplit; [iPureIntro; exact HentryValidT | done]
      | idtac ];
      iAssert (writeSuccessAccessEntriesOwn (entryT :: remainingT))%I
        with "[HentryTarget HremainingOwn2]" as "HentryListTarget";
      [ iEval (cbn [writeSuccessAccessEntriesOwn]);
        iFrame; done
      | idtac ];
      iAssert
        (writeSuccessAccessListsCopiedScratch spT baseT
          (length entriesT) (length processedT) entryT)%I
        with "[HsavedX22 HbasePtr Htotal Hprocessed HcopiedFinal
          HscratchStack HstorageScratch]" as "HscratchTarget";
      [ iEval (unfold writeSuccessAccessListsCopiedScratch);
        iFrame; done
      | idtac ];
      iAssert
        (writeSuccessAccessListsInvariant spT baseT entriesT processedT
          (entryT :: remainingT) bytesT prefixT suffixT)%I
        with "[HbytesConcatRest HbytesLenRest HprefixLenRest HsuffixLenRest
          HentriesLenRest HbaseLowerRest HbaseUpperRest]"
          as "HinvTarget";
      [ iEval (unfold writeSuccessAccessListsInvariant);
        iSplit; [iPureIntro; reflexivity | idtac];
        iSplit; [iPureIntro; reflexivity | idtac];
        iSplit; [iPureIntro; reflexivity | idtac];
        iSplit; [iPureIntro; reflexivity | idtac];
        iSplit; [iExact "HbytesConcatRest" | idtac];
        iSplit; [iExact "HbytesLenRest" | idtac];
        iSplit; [iExact "HprefixLenRest" | idtac];
        iSplit; [iExact "HsuffixLenRest" | idtac];
        iSplit; [iExact "HentriesLenRest" | idtac];
        iSplit; [iPureIntro; exact HspAlign2 | idtac];
        iSplit; [iPureIntro; exact HspLower2 | idtac];
        iSplit; [iPureIntro; exact HspUpper2 | idtac];
        iSplit; [iExact "HbaseLowerRest" | idtac];
        iSplit; [iExact "HbaseUpperRest" | idtac];
        done
      | idtac ];
      iFrame "HsysCurrent Hother Hx2Current Hx10 Hx19 Hx11 Hx22Current
        Hx27Current HbasePrefix HbaseSuffix HprocessedOwn
        HentryListTarget HscratchTarget Hmmio Htrace HP HinvTarget Hloop" ].
  Unshelve.
  all: try (rewrite /find_in_context /FindRegMapsTo /=;
    iExists (RKCol zesu_ram_sys_regs); iFrame).
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.
