Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_32 Require Import a1505c_spec.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1505c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15078.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_1505c_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

#[local] Hint Rewrite write_success_1505c_current_unsigned using lia :
  lithium_rewrite.

Definition writeSuccessTransactionsMachine15060 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  writeSuccessTransactionsMachine15048WithX16AndScratch
    sp base transactions processed transaction
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      transaction 96)
    (writeSuccessTransactionsScratch15078
      sp base transactions processed transaction).

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15060) := I.

Definition writeSuccessTransactionsAt15060Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine15060
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15060Spec) := I.

Definition writeSuccessTransactionsAt1505cBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (writeSuccessTransactionsMachine1505c
     sp base transactions processed transaction ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt1505cBlock) := I.

Definition writeSuccessTransactionsAt15060Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (writeSuccessTransactionsMachine15060
     sp base transactions processed transaction ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15060Block) := I.

Lemma write_success_transactions_chunk_1505c_store_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x1505c (zesu_sd_spec 0x1505c "x16" "x2" 216) -∗
  instr_body 0x15060 (writeSuccessTransactionsAt15060Spec P) -∗
  instr_body 0x1505c (writeSuccessTransactionsAt1505cBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  iIntros "Hsd Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsAt1505cBlock) in "Hentry".
  iDestruct "Hentry" as
    "(Hmachine & Harray & Hframe & Hfacts & %Hcurrent & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (rewrite /writeSuccessTransactionsMachine1505c
    /writeSuccessTransactionsMachine15048WithX16AndScratch
    /writeSuccessTransactionsScratch1505c) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & Hx21 & Hx2 & Hx5 & Hx6 & Hx7 & Hx8 & Hx9 &
      Hx10 & Hx11 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 & Hx18 &
      Hx19 & Hx20 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27 & Hx28 & Hx29 &
      Hx30 & Hx31 & Hscratch & _)".
  iDestruct "Hscratch" as
    "(Hlower & H104 & H112 & H120 & H128 & Hscratch136 & H144 & H152 &
      Hscratch160_64 & H224 & H232 & H240 & H248 & H256 & H272 & H280 &
      H1664 & H1672 & H1680 & _)".
  iDestruct (mem_mapsto_uninit_split 56 with "Hscratch160_64") as
    "[Hscratch160 Hscratch216]".
  { lia. }
  have Hscratch216Address :
    (bv_unsigned sp + 160 + 56 = bv_unsigned sp + 216)%Z by lia.
  iEval (rewrite Hscratch216Address) in "Hscratch216".
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsRebuilt".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply ("Hsd" with "[-]").
  rewrite /zesu_sd_spec /rv64_sd_spec.
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 96),
    sp.
  iFrame "Hsys Hx16 Hx2 Hscratch216".
  iSplit.
  { iPureIntro. exact HspAlign. }
  iSplit.
  { iPureIntro. lia. }
  rewrite instr_pre'_eq.
  iNext. iIntros "Hpost".
  iDestruct "Hpost" as "(HsysPost & Hx16Post & Hx2Post & Hscratch216Post & _)".
  iAssert (writeSuccessTransactionsMachine15060
    sp base transactions processed transaction) with
    "[-Harray Hframe Hnext]"
    as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine15060
      /writeSuccessTransactionsMachine15048WithX16AndScratch
      /writeSuccessTransactionsScratch15078.
    iFrame "HsysPost Hother Hx21 Hx2Post Hx5 Hx6 Hx7 Hx8 Hx9 Hx10 Hx11
      Hx12 Hx13 Hx14 Hx15 Hx16Post Hx17 Hx18 Hx19 Hx20 Hx23 Hx24 Hx25
      Hx26 Hx27 Hx28 Hx29 Hx30 Hx31 Hlower H104 H112 H120 H128
      Hscratch136 H144 H152 Hscratch160 Hscratch216Post H224 H232 H240
      H248 H256 H272 H280 H1664 H1672 H1680". }
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsFinal".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply "Hnext".
  rewrite /writeSuccessTransactionsAt15060Spec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "HmachineFinal Harray Hframe HfactsFinal".
Qed.

Lemma write_success_transactions_chunk_1505c_store
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x1505c (Some IslaTraces.write_success_32.a1505c.a1505c) -∗
  instr_body 0x15060 (writeSuccessTransactionsAt15060Spec P) -∗
  instr_body 0x1505c (writeSuccessTransactionsAt1505cSpec P).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof
    (IslaTraces.write_success_32.a1505c_spec.a1505c_spec 0x1505c with
      "Hinstr") as "Hsd".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt1505cSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_1505c_store_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hsd Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt1505cBlock.
  iFrame.
  iPureIntro.
  repeat split; try assumption.
  apply write_success_1505c_current_unsigned; lia.
Qed.

Lemma write_success_transactions_chunk_15060
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15078 (writeSuccessTransactionsAt15078Spec P) -∗
  instr_body 0x15060 (writeSuccessTransactionsAt15060Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  have Hword265Bytes :
      forall (bs : list (bv 8)),
        (273 <= length bs)%nat ->
        (bv_or
           (bv_shiftl
           (bv_or
              (bv_or
                 (bv_shiftl (bv_zero_extend 64
                   (default (BV 8 0) (bs !! 272%nat))) (BV 64 24))
                 (bv_shiftl (bv_zero_extend 64
                   (default (BV 8 0) (bs !! 271%nat))) (BV 64 16)))
              (bv_or
                 (bv_shiftl (bv_zero_extend 64
                   (default (BV 8 0) (bs !! 270%nat))) (BV 64 8))
                 (bv_zero_extend 64 (default (BV 8 0) (bs !! 269%nat)))))
           (BV 64 32))
           (bv_or
              (bv_or
                 (bv_shiftl (bv_zero_extend 64
                   (default (BV 8 0) (bs !! 268%nat))) (BV 64 24))
                 (bv_shiftl (bv_zero_extend 64
                   (default (BV 8 0) (bs !! 267%nat))) (BV 64 16)))
              (bv_or
                 (bv_shiftl (bv_zero_extend 64
                   (default (BV 8 0) (bs !! 266%nat))) (BV 64 8))
                 (bv_zero_extend 64 (default (BV 8 0) (bs !! 265%nat)))))) =
        Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 265 bs))).
  { intros bs Hlen.
    have Hbyte (i : nat) (Hi : (i < length bs)%nat) :
        bs !! i = Some (default (BV 8 0) (bs !! i)).
    { destruct (nth_lookup_or_length bs i (BV 8 0)) as [Hlookup|Hlookup].
      - rewrite Hlookup. reflexivity.
      - lia. }
    have Hslice :
        take 8 (drop 265 bs) =
        [default (BV 8 0) (bs !! 265%nat);
         default (BV 8 0) (bs !! 266%nat);
         default (BV 8 0) (bs !! 267%nat);
         default (BV 8 0) (bs !! 268%nat);
         default (BV 8 0) (bs !! 269%nat);
         default (BV 8 0) (bs !! 270%nat);
         default (BV 8 0) (bs !! 271%nat);
         default (BV 8 0) (bs !! 272%nat)]%list.
    { apply list_eq. intros i.
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 265%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 266%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 267%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 268%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 269%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 270%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 271%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 272%nat ltac:(lia)); reflexivity).
      all: try (rewrite lookup_take_ge; [done|lia]).
      }
    rewrite Hslice.
    unfold little_endian_to_bv, little_endian_to_Z.
    rewrite !fmap_cons.
    cbn.
    apply bv_eq.
    bv_simplify.
    bitblast as i.
    all: (f_equal; lia). }
  have Hword273Bytes :
      forall (bs : list (bv 8)),
        (281 <= length bs)%nat ->
        (bv_or
           (bv_shiftl
           (bv_or
              (bv_or
                 (bv_shiftl (bv_zero_extend 64
                   (default (BV 8 0) (bs !! 280%nat))) (BV 64 24))
                 (bv_shiftl (bv_zero_extend 64
                   (default (BV 8 0) (bs !! 279%nat))) (BV 64 16)))
              (bv_or
                 (bv_shiftl (bv_zero_extend 64
                   (default (BV 8 0) (bs !! 278%nat))) (BV 64 8))
                 (bv_zero_extend 64 (default (BV 8 0) (bs !! 277%nat)))))
           (BV 64 32))
           (bv_or
              (bv_or
                 (bv_shiftl (bv_zero_extend 64
                   (default (BV 8 0) (bs !! 276%nat))) (BV 64 24))
                 (bv_shiftl (bv_zero_extend 64
                   (default (BV 8 0) (bs !! 275%nat))) (BV 64 16)))
              (bv_or
                 (bv_shiftl (bv_zero_extend 64
                   (default (BV 8 0) (bs !! 274%nat))) (BV 64 8))
                 (bv_zero_extend 64 (default (BV 8 0) (bs !! 273%nat)))))) =
        Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 273 bs))).
  { intros bs Hlen.
    have Hbyte (i : nat) (Hi : (i < length bs)%nat) :
        bs !! i = Some (default (BV 8 0) (bs !! i)).
    { destruct (nth_lookup_or_length bs i (BV 8 0)) as [Hlookup|Hlookup].
      - rewrite Hlookup. reflexivity.
      - lia. }
    have Hslice :
        take 8 (drop 273 bs) =
        [default (BV 8 0) (bs !! 273%nat);
         default (BV 8 0) (bs !! 274%nat);
         default (BV 8 0) (bs !! 275%nat);
         default (BV 8 0) (bs !! 276%nat);
         default (BV 8 0) (bs !! 277%nat);
         default (BV 8 0) (bs !! 278%nat);
         default (BV 8 0) (bs !! 279%nat);
         default (BV 8 0) (bs !! 280%nat)]%list.
    { apply list_eq. intros i.
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 273%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 274%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 275%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 276%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 277%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 278%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 279%nat ltac:(lia)); reflexivity).
      destruct i as [|i]; cbn.
      all: try (rewrite lookup_take; [|lia]; rewrite lookup_drop; cbn;
        rewrite (Hbyte 280%nat ltac:(lia)); reflexivity).
      all: try (rewrite lookup_take_ge; [done|lia]).
      }
    rewrite Hslice.
    unfold little_endian_to_bv, little_endian_to_Z.
    rewrite !fmap_cons.
    cbn.
    apply bv_eq.
    bv_simplify.
    bitblast as i.
    all: (f_equal; lia). }
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_1505c_current_unsigned; try lia.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_1505c_current_unsigned; try lia.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: iRename select (reg_col _)%I into "HotherFinal".
  first
    [ iRename select (reg_col zesu_ram_sys_regs)%I into "HsysFinal"
    | iRename select ("rv_enable_pmp" ↦ᵣ _)%I into "Hs0";
      iRename select ("rv_enable_misaligned_access" ↦ᵣ _)%I into "Hs1";
      iRename select ("rv_ram_base" ↦ᵣ _)%I into "Hs2";
      iRename select ("rv_ram_size" ↦ᵣ _)%I into "Hs3";
      iRename select ("rv_rom_base" ↦ᵣ _)%I into "Hs4";
      iRename select ("rv_rom_size" ↦ᵣ _)%I into "Hs5";
      iRename select ("rv_clint_base" ↦ᵣ _)%I into "Hs6";
      iRename select ("rv_clint_size" ↦ᵣ _)%I into "Hs7";
      iRename select ("rv_htif_tohost" ↦ᵣ _)%I into "Hs8";
      iRename select ("cur_privilege" ↦ᵣ _)%I into "Hs9";
      iRename select ("misa" ↦ᵣ _)%I into "Hs10";
      iRename select ("mtvec" ↦ᵣ _)%I into "Hs11";
      iRename select ("mstatus" ↦ᵣ _)%I into "Hs12";
      iRename select ("satp" ↦ᵣ _)%I into "Hs13";
      iAssert (reg_col zesu_ram_sys_regs)%I
        with "[Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13]"
        as "HsysFinal";
      [ rewrite !reg_col_cons reg_col_nil; iFrame;
        repeat iSplit; iPureIntro; done
      | ] ].
  all: iRename select
    ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)%I
    into "HarrayFinal".
  all: iRename select
    (writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    into "HframeFinal".
  all: iAssert (writeSuccessTransactionsMachine15078
    sp base transactions processed transaction)%I
    with "[-HarrayFinal HframeFinal]" as "HmachineFinal";
    [ rewrite /writeSuccessTransactionsMachine15078
        /writeSuccessTransactionsScratch15078;
      iFrame; liARun
    | ].
  Unshelve.
  all: try subst LET8.
  all: try iFrame.
  all: try iFrame.
  all: try prepare_sidecond.
  all: try unLET.
  all: try subst LET4.
  all: try iFrame.
  all: try liShow.
  all: try iFrame.
  all: try subst LET8.
  all: try iFrame.
  all: try (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionWord,
    WriteSuccessTransactionsSpec.writeSuccessTransactionByte;
    eapply Hword265Bytes; lia).
  all: try (rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionWord;
    rewrite !fmap_cons; cbn; iFrame).
  all: iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  all: iFrame "HmachineFinal HarrayFinal HframeFinal".
  all: rewrite /writeSuccessTransactionsLoadFacts.
  all: repeat iSplit; try iPureIntro; try assumption; try done.
  Unshelve.
  all: try subst LET10.
  all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try reflexivity.
  all: (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionWord,
    WriteSuccessTransactionsSpec.writeSuccessTransactionByte;
    eapply Hword265Bytes; lia).
  Unshelve.
  all: try subst LET4.
  all: try unLET.
  all: try (rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionWord;
    cbn; bv_solve).
  all: try (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionWord,
    WriteSuccessTransactionsSpec.writeSuccessTransactionByte;
    rewrite <- (Hword273Bytes
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction));
    [iFrame|lia]).
  all: try (iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ;
    iFrame "HmachineFinal HarrayFinal HframeFinal";
    rewrite /writeSuccessTransactionsLoadFacts;
    repeat iSplit; try iPureIntro; try assumption; try done).
Qed.

Lemma write_success_transactions_chunk_1505c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15078 (writeSuccessTransactionsAt15078Spec P) -∗
  instr_body 0x1505c (writeSuccessTransactionsAt1505cSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof "Hlookup" as "#Hlookup5c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup5c".
  iPoseProof ("Hlookup5c" $! 0x1505c) as "Hinstr5c".
  iSpecialize ("Hinstr5c" with "[]").
  { iPureIntro. rewrite Index.lookup_a1505c. done. }
  iEval (rewrite Index.lookup_a1505c) in "Hinstr5c".
  iPoseProof (write_success_transactions_chunk_15060 P with
    "Hlookup Hcode Hnext") as "H60".
  iApply (write_success_transactions_chunk_1505c_store P with
    "Hinstr5c H60").
Qed.
