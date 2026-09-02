From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f60.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f64.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_14f60_transaction_byte_lookup
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

Lemma write_success_14f60_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

Lemma write_success_14f60_array_element_address (current offset : Z) :
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

#[local] Hint Rewrite write_success_14f60_current_unsigned using lia :
  lithium_rewrite.

Definition writeSuccessTransactionsAt14f60Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (x14 : valu) : iProp Sigma :=
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
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 280)) ∗
   ⌜valu_has_shape x14 (BitsShape 64)⌝ ∗
   "x14" ↦ᵣ x14 ∗
   "x26" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 184) ∗
   "x8" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactions14f64Frame
     sp base transactions processed transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14f60Block) := I.

Lemma write_success_transactions_chunk_14f60_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) (x14 : valu) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f64 (writeSuccessTransactionsAt14f64Spec P) -∗
  instr_body 0x14f60 (writeSuccessTransactionsAt14f60Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail x14).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_14f60_current_unsigned; try lia.
  all: try (iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 281,
      tt)ₗ).
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_14f60_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try apply write_success_14f60_transaction_byte_lookup; try lia.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try apply write_success_14f60_array_element_address; try lia.
  Unshelve.
  all: lazymatch goal with
  | Hlength : length
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes ?transaction) =
      288%nat,
    Hunsigned : bv_unsigned (Z_to_bv 64 ?current) = ?current |- _ =>
      try rewrite Hunsigned;
      rewrite /IslarisMemory.array_region_start;
      replace (current + 281 - current)%Z with 281%Z by lia; cbn;
      iExists
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
         WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 281, tt)ₗ;
      iSplit;
      [ iPureIntro;
        change (take 1
          (drop 281
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
              transaction)) =
          [WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 281]);
        assert (Hbyte :
          drop 281
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
              transaction) !! 0%nat =
          Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 281));
        [ rewrite lookup_drop; cbn;
          apply write_success_14f60_transaction_byte_lookup; lia
        | rewrite (take_S_r _ 0 _ Hbyte); rewrite take_0; reflexivity ]
      | ];
      iSplit; [iPureIntro; lia |];
      iIntros "Hprefix281 Hsuffix282";
      assert (Hstart :
        Z.to_nat (281 `div` Z.of_N (8 `div` 8)) = 281%nat);
      [ vm_compute; reflexivity | ];
      iEval (rewrite Hstart) in "Hprefix281 Hsuffix282";
      try rewrite Hunsigned;
      rewrite Z.add_0_r;
      iFrame "Hprefix281 Hsuffix282";
      repeat iSplit; try iPureIntro; try lia;
      try apply write_success_14f60_transaction_byte_lookup; try lia;
      liARun
  end.
  iExists (tail, suffix, prefix, bytes, remaining, transactions, sp, tt)ₗ.
  iFrame.
  repeat iSplit; try (iPureIntro; assumption).
  all: try done.
  Unshelve. all: try prepare_sidecond.
  all: try assumption.
  all: try solve_zesu_ld_array_at.
  all: try apply write_success_14f60_transaction_byte_lookup; try lia.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try done.
Qed.

Lemma write_success_transactions_chunk_14f60
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f64 (writeSuccessTransactionsAt14f64Spec P) -∗
  instr_body 0x14f60 (writeSuccessTransactionsAt14f60Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt14f60Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hsys & Hx25 & Hx24 & Hx9 & Hx23 & Hx11 & Hx12 & Hx13 & Hx26 &
      Hx8 & Hx10 & Hprefix280 & Hbyte280 & Hsuffix281 & Hmachine &
      Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (unfold writeSuccessTransactions14f60Frame) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hstack0 & Hstack1 & Hstack2 & Hstack3 & HstackWord152 &
      HstackWord144 & HstackWord136 & Hstack4 & Hstack5 &
      HstackWord176 & Hstack6 & Hx2 & Hother & _)".
  iDestruct (reg_col_lookup
    (delete 6%nat
      (delete 16%nat
        (delete 7%nat
          (delete 7%nat
            (delete 18%nat
              (delete 7%nat
                (delete 20%nat writeSuccessTransactions14f1cOtherRegShapes)))))))
    6%nat (KindReg "x14", BitsShape 64) with "Hother") as
    (x14 Hx14Shape) "(Hx14 & Hother)".
  { vm_compute. reflexivity. }
  iAssert (writeSuccessTransactions14f64Frame
      sp base transactions processed transaction)
    with "[Hstack0 Hstack1 Hstack2 Hstack3 HstackWord152 HstackWord144
      HstackWord136 Hstack4 Hstack5 HstackWord176 Hstack6 Hx2 Hother]"
      as "Hmachine".
  { rewrite /writeSuccessTransactions14f64Frame. iFrame. }
  iPoseProof (mem_mapsto_array_recombine_u8_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    280 (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
      transaction 280)
    (base + 288 * Z.of_nat (length processed) + 281)
    (base + 288 * Z.of_nat (length processed) + 280) with
    "Hprefix280 Hsuffix281 Hbyte280 [] [] []") as "Harray".
  { iPureIntro. apply write_success_14f60_transaction_byte_lookup. lia. }
  { iPureIntro. lia. }
  { iPureIntro. lia. }
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_chunk_14f60_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail x14
    with "Hlookup Hcode Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt14f60Block.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_14f60_current_unsigned; try lia.
  all: try iFrame.
  all: try done.
Qed.
