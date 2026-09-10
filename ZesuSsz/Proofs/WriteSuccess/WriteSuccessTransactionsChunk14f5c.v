From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f5c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f60.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_14f5c_transaction_byte_lookup
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (index : nat) :
  (index < length
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction))%nat ->
  WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction !! index =
    Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
      transaction index).
Proof.
  intros Hindex.
  rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionByte.
  destruct (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
    transaction !! index) eqn:Hlookup; [done |].
  apply lookup_ge_None_1 in Hlookup. lia.
Qed.

Lemma write_success_14f5c_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

Lemma write_success_14f5c_array_element_address (current offset : Z) :
  (0 <= offset)%Z ->
  current + offset =
    current + 1 * IslarisMemory.array_region_start 8 current
      (current + offset).
Proof.
  intros Hoffset.
  rewrite /IslarisMemory.array_region_start.
  replace (current + offset - current)%Z with offset by lia.
  rewrite Zdiv_1_r Z2Nat.id; lia.
Qed.

#[local] Hint Rewrite write_success_14f5c_current_unsigned using lia :
  lithium_rewrite.

Definition writeSuccessTransactionsAt14f5cBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x25" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0) ∗
   "x24" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8) ∗
   "x9" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 16) ∗
   "x23" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24) ∗
   "x11" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 160) ∗
   "x12" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168) ∗
   "x13" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176) ∗
   "x26" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 184) ∗
   "x8" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactions14f60Frame
     sp base transactions processed transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14f5cBlock) := I.

Lemma write_success_transactions_chunk_14f5c_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f60 (writeSuccessTransactionsAt14f60Spec P) -∗
  instr_body 0x14f5c (writeSuccessTransactionsAt14f5cBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_14f5c_current_unsigned; try lia.
  all: try (iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 280,
      tt)ₗ).
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_14f5c_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try apply write_success_14f5c_transaction_byte_lookup; try lia.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try apply write_success_14f5c_array_element_address; try lia.
  Unshelve.
  all: lazymatch goal with
  | Hlength : length
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes ?transaction) =
      288%nat,
    Hunsigned : bv_unsigned (Z_to_bv 64 ?current) = ?current |- _ =>
      try rewrite Hunsigned;
      rewrite /IslarisMemory.array_region_start;
      replace (current + 280 - current)%Z with 280%Z by lia; cbn;
      iExists
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
         WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 280, tt)ₗ;
      iSplit;
      [ iPureIntro;
        change (take 1
          (drop 280
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
              transaction)) =
          [WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 280]);
        assert (Hbyte :
          drop 280
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
              transaction) !! 0%nat =
          Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 280));
        [ rewrite lookup_drop; cbn;
          apply write_success_14f5c_transaction_byte_lookup; lia
        | rewrite (take_S_r _ 0 _ Hbyte); rewrite take_0; reflexivity ]
      | ];
      iSplit; [iPureIntro; lia |];
      iIntros "Hprefix280 Hsuffix281";
      assert (Hstart :
        Z.to_nat (280 `div` Z.of_N (8 `div` 8)) = 280%nat);
      [ vm_compute; reflexivity | ];
      iEval (rewrite Hstart) in "Hprefix280 Hsuffix281";
      try rewrite Hunsigned;
      rewrite Z.add_0_r;
      iFrame "Hprefix280 Hsuffix281";
      repeat iSplit; try iPureIntro; try lia;
      try apply write_success_14f5c_transaction_byte_lookup; try lia;
      liARun
  end.
  iExists (tail, suffix, prefix, bytes, remaining, transactions, sp, tt)ₗ.
  iFrame.
  repeat iSplit; try (iPureIntro; assumption).
  all: try done.
  Unshelve. all: try prepare_sidecond.
  all: try assumption.
  all: try solve_zesu_ld_array_at.
  all: try apply write_success_14f5c_transaction_byte_lookup; try lia.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try done.
Qed.

Lemma write_success_transactions_chunk_14f5c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f60 (writeSuccessTransactionsAt14f60Spec P) -∗
  instr_body 0x14f5c (writeSuccessTransactionsAt14f5cSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt14f5cSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hsys & Hx25 & Hx24 & Hx9 & Hx23 & Hx11 & Hx12 & Hx13 & Hx26 &
      Hx8 & Hx10 & Hprefix192 & Hword192 & Hsuffix200 & Hmachine &
      Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (unfold writeSuccessTransactions14f5cFrame) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hstack0 & Hstack1 & Hstack2 & Hstack3 & HstackWord152 &
      HstackWord144 & HstackWord136 & Hstack4 & Hstack5 &
      HstackWord176 & Hstack6 & Hx2 & Hother & _)".
  iAssert (writeSuccessTransactions14f60Frame
      sp base transactions processed transaction)
    with "[Hstack0 Hstack1 Hstack2 Hstack3 HstackWord152 HstackWord144
      HstackWord136 Hstack4 Hstack5 HstackWord176 Hstack6 Hx2 Hother]"
      as "Hmachine".
  { rewrite /writeSuccessTransactions14f60Frame. iFrame. }
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    192
    (base + 288 * Z.of_nat (length processed) + 200)
    (base + 288 * Z.of_nat (length processed) + 192) with
    "Hprefix192 Hsuffix200 Hword192 [] [] []") as "Harray".
  { iPureIntro. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite Hlength. lia. }
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_chunk_14f5c_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    with "Hlookup Hcode Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt14f5cBlock.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_14f5c_current_unsigned; try lia.
  all: try iFrame.
  all: try done.
Qed.
