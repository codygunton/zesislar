From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundarySpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f70.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.
#[local] Typeclasses Opaque reg_col.

Lemma write_success_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

#[local] Hint Rewrite write_success_current_unsigned using lia : lithium_rewrite.

Lemma write_success_array_element_address (current offset : Z) :
  (0 <= offset)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current ->
  bv_unsigned (Z_to_bv 64 current) + offset =
    current + 1 * IslarisMemory.array_region_start 8 current
      (bv_unsigned (Z_to_bv 64 current) + offset).
Proof.
  intros Hoffset Hunsigned.
  rewrite Hunsigned /IslarisMemory.array_region_start.
  cbn.
  replace (current + offset - current)%Z with offset by lia.
  rewrite Zdiv_1_r Z2Nat.id; lia.
Qed.

Ltac solve_write_success_current_address :=
  lazymatch goal with
  | Hunsigned : bv_unsigned (Z_to_bv 64 ?current) = ?current |- _ =>
      apply write_success_array_element_address; [lia | exact Hunsigned]
  end.

Definition writeSuccessTransactionsMachine14f68Block
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  (∃ x16 x17 x5,
   ⌜valu_has_shape x16 (BitsShape 64)⌝ ∗
   ⌜valu_has_shape x17 (BitsShape 64)⌝ ∗
   ⌜valu_has_shape x5 (BitsShape 64)⌝ ∗
   "x16" ↦ᵣ x16 ∗
   "x17" ↦ᵣ x17 ∗
   "x5" ↦ᵣ x5 ∗
   reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions14f70OtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   "x11" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 160) ∗
   "x12" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168) ∗
   "x13" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 280)) ∗
   "x14" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 281)) ∗
   "x15" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 282)) ∗
   "x23" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 184) ∗
   writeSuccessTransactionsScratch14f68
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsMachine14f68Block) := I.

Lemma write_success_transaction_byte_lookup
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

Lemma write_success_advance_transaction_byte `{!islaG Sigma}
    (base : Z) (values : list (bv 8)) (index : nat)
    (current next : bv 8) :
  values !! index = Some current ->
  values !! S index = Some next ->
  base ↦ₘ∗ take index values -∗
  (base + Z.of_nat index) ↦ₘ current -∗
  (base + Z.of_nat (S index)) ↦ₘ∗ drop (S index) values -∗
  base ↦ₘ∗ take (S index) values ∗
  (base + Z.of_nat (S index)) ↦ₘ next ∗
  (base + Z.of_nat (S (S index))) ↦ₘ∗ drop (S (S index)) values.
Proof.
  iIntros (Hcurrent Hnext) "Hprefix Hcurrent Hsuffix".
  iEval (rewrite -IslarisMemory.mem_mapsto_array_singleton) in "Hcurrent".
  iPoseProof (IslarisMemory.mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    (take index values) [current] index with "Hprefix") as "Hcombine".
  { rewrite length_take. apply Nat.min_l.
    apply lookup_lt_Some in Hcurrent. lia. }
  have HcurrentAddress :
      (base + Z.of_N (8 `div` 8) * Z.of_nat index)%Z =
      (base + Z.of_nat index)%Z.
  { change (base + 1 * Z.of_nat index = base + Z.of_nat index)%Z. lia. }
  iEval (rewrite HcurrentAddress) in "Hcombine".
  iSpecialize ("Hcombine" with "Hcurrent").
  iEval (rewrite -(take_S_r values index current Hcurrent)) in "Hcombine".
  iEval (rewrite (drop_S values next (S index) Hnext)) in "Hsuffix".
  iDestruct (IslarisMemory.mem_mapsto_array_app 8%N
    (base + Z.of_nat (S index)) (DfracOwn 1) [next]
    (drop (S (S index)) values) with "Hsuffix") as
    "[Hnext Hsuffix]".
  iEval (rewrite IslarisMemory.mem_mapsto_array_singleton) in "Hnext".
  iFrame "Hcombine Hnext".
  iEval (cbn) in "Hsuffix".
  replace
    (base + Z.of_nat (S index) + 1)%Z with
    (base + Z.of_nat (S (S index)))%Z by lia.
  iExact "Hsuffix".
Qed.

Lemma write_success_append_transaction_byte `{!islaG Sigma}
    (base : Z) (values : list (bv 8)) (index : nat) (value : bv 8) :
  values !! index = Some value ->
  base ↦ₘ∗ take index values -∗
  (base + Z.of_nat index) ↦ₘ value -∗
  base ↦ₘ∗ take (S index) values.
Proof.
  iIntros (Hlookup) "Hprefix Hvalue".
  iEval (rewrite -IslarisMemory.mem_mapsto_array_singleton) in "Hvalue".
  iPoseProof (IslarisMemory.mem_mapsto_array_app_combine_at 8%N base
    (DfracOwn 1) (take index values) [value] index with "Hprefix") as
    "Hcombine".
  { rewrite length_take. apply Nat.min_l.
    apply lookup_lt_Some in Hlookup. lia. }
  have Haddress :
      (base + Z.of_N (8 `div` 8) * Z.of_nat index)%Z =
      (base + Z.of_nat index)%Z.
  { change (base + 1 * Z.of_nat index = base + Z.of_nat index)%Z. lia. }
  iEval (rewrite Haddress) in "Hcombine".
  iSpecialize ("Hcombine" with "Hvalue").
  iEval (rewrite -(take_S_r values index value Hlookup)) in "Hcombine".
  iExact "Hcombine".
Qed.

Lemma write_success_recombine_transaction_byte `{!islaG Sigma}
    (base : Z) (values : list (bv 8)) (index : nat) (value : bv 8) :
  values !! index = Some value ->
  base ↦ₘ∗ take index values -∗
  (base + Z.of_nat index) ↦ₘ value -∗
  (base + Z.of_nat (S index)) ↦ₘ∗ drop (S index) values -∗
  base ↦ₘ∗ values.
Proof.
  iIntros (Hlookup) "Hprefix Hvalue Hsuffix".
  iPoseProof (write_success_append_transaction_byte base values index value
    Hlookup with "Hprefix Hvalue") as "Hprefix".
  iPoseProof (IslarisMemory.mem_mapsto_array_app_combine_at 8%N base
    (DfracOwn 1) (take (S index) values) (drop (S index) values)
    (S index) with "Hprefix") as "Hcombine".
  { rewrite length_take. apply Nat.min_l.
    apply lookup_lt_Some in Hlookup. lia. }
  have Haddress :
      (base + Z.of_N (8 `div` 8) * Z.of_nat (S index))%Z =
      (base + Z.of_nat (S index))%Z.
  { change (base + 1 * Z.of_nat (S index) =
      base + Z.of_nat (S index))%Z. lia. }
  iEval (rewrite Haddress) in "Hcombine".
  iSpecialize ("Hcombine" with "Hsuffix").
  iEval (rewrite take_drop) in "Hcombine".
  iExact "Hcombine".
Qed.

Definition writeSuccessTransactionsAt14f68Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactionsMachine14f68Block
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

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14f68Block) := I.

Lemma write_success_transactions_chunk_14f68_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f70 (writeSuccessTransactionsAt14f70Spec P) -∗
  instr_body 0x14f68 (writeSuccessTransactionsAt14f68Block P sp base
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
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try solve_write_success_current_address.
  all: try liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: lazymatch goal with
  | Hlength : length
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes ?transaction) =
      288%nat,
    Hunsigned : bv_unsigned (Z_to_bv 64 ?current) = ?current |- _ =>
      try rewrite Hunsigned;
      rewrite /IslarisMemory.array_region_start;
      replace (current + 283 - current)%Z with 283%Z by lia; cbn;
      iExists
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
         WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 283, tt)ₗ;
      iSplit;
      [ iPureIntro;
        change (take 1
          (drop 283
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
              transaction)) =
          [WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 283]);
        assert (Hbyte :
          drop 283
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
              transaction) !! 0%nat =
          Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 283));
        [ rewrite lookup_drop; cbn;
          apply write_success_transaction_byte_lookup; lia
        | rewrite (take_S_r _ 0 _ Hbyte); rewrite take_0; reflexivity ]
      | ];
      iSplit; [iPureIntro; lia |];
      iIntros "Hbefore Hafter";
      iFrame;
      repeat iSplit; try iPureIntro; try lia;
      try apply write_success_transaction_byte_lookup; try lia;
      liARun
  end.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try apply write_success_transaction_byte_lookup; try lia.
  all: try iFrame.
  all: lazymatch goal with
  | Hunsigned : bv_unsigned (Z_to_bv 64 ?current) = ?current |- _ =>
      try rewrite Hunsigned;
      rewrite /IslarisMemory.array_region_start;
      replace (current + 284 - (current + 0 + 284))%Z with 0%Z by lia;
      change (current + 284 = current + 0 + 284 + 1 * Z.of_nat 0)%Z;
      lia
  end.
  Unshelve.
  all: lazymatch goal with
  | Hlength : length
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes ?transaction) =
      288%nat,
    Hunsigned : bv_unsigned (Z_to_bv 64 ?current) = ?current |- _ =>
      try rewrite Hunsigned;
      rewrite /IslarisMemory.array_region_start;
      replace (current + 284 - (current + 0 + 284))%Z with 0%Z by lia;
      cbn;
      iExists
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
         WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 284, tt)ₗ;
      iSplit;
      [ iPureIntro;
        change (take 1
          (drop 0
            (drop 284
              (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
                transaction))) =
          [WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 284]);
        rewrite drop_0;
        assert (Hbyte :
          drop 284
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
              transaction) !! 0%nat =
          Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 284));
        [ rewrite lookup_drop; cbn;
          apply write_success_transaction_byte_lookup; lia
        | rewrite (take_S_r _ 0 _ Hbyte); rewrite take_0; reflexivity ]
      | ];
      iSplit; [iPureIntro; rewrite length_drop; lia |];
      iIntros "Hempty284 Hsuffix285";
      iRename select
        ((current + 0) ↦ₘ∗ take 283
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction))%I into "Hprefix283";
      iRename select
        ((current + 283) ↦ₘ
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 283))%I into "Hbyte283";
      iEval (rewrite Z.add_0_r) in "Hprefix283";
      assert (Hlookup283 :
          WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction !! 283%nat =
          Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 283));
      [ apply write_success_transaction_byte_lookup; lia | ];
      iPoseProof (write_success_append_transaction_byte current _ 283 _
        Hlookup283 with "Hprefix283 Hbyte283") as "Hprefix284";
      assert (Hstart :
          Z.to_nat (0 `div` Z.of_N (8 `div` 8)) = 0%nat);
      [ vm_compute; reflexivity | ];
      iEval (rewrite Hstart drop_drop) in "Hsuffix285";
      iEval (cbn) in "Hsuffix285";
      assert (HsuffixAddress :
          (current + 0 + 284 + 1 * 1)%Z = (current + 285)%Z);
      [ lia | ];
      iEval (rewrite HsuffixAddress) in "Hsuffix285";
      iAssert ((current + 285) ↦ₘ∗ drop 285
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
          transaction))%I with "[Hsuffix285]" as "Hsuffix285Expected";
      [ iExact "Hsuffix285" | ];
      try rewrite Hunsigned;
      rewrite Z.add_0_r;
      iFrame "Hprefix284 Hsuffix285Expected";
      repeat iSplit; try iPureIntro; try lia;
      try apply write_success_transaction_byte_lookup; try lia;
      liARun
  end.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: lazymatch goal with
  | Hlength : length
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes ?transaction) =
      288%nat,
    Hunsigned : bv_unsigned (Z_to_bv 64 ?current) = ?current |- _ =>
      iRename select
        (_ ↦ₘ∗ take 284
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction))%I into "Hprefix284Final";
      iRename select
        (_ ↦ₘ
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 284))%I into "Hbyte284Final";
      iRename select
        (_ ↦ₘ∗ drop 285
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction))%I into "Hsuffix285Final";
      assert (Hlookup284Final :
          WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction !! 284%nat =
          Some (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 284));
      [ apply write_success_transaction_byte_lookup; lia | ];
      iPoseProof (write_success_recombine_transaction_byte current _ 284 _
        Hlookup284Final with
        "Hprefix284Final Hbyte284Final Hsuffix285Final") as "HarrayFinal";
      iRename select (writeSuccessTransactionsCurrentPhaseFrame P sp base
        transaction transactions processed remaining bytes prefix suffix
        tail)%I into "HframeFinal";
      iAssert (writeSuccessTransactionsMachine14f70 sp base transactions
        processed transaction) with "[-HarrayFinal HframeFinal]"
        as "HmachineFinal";
      [ rewrite /writeSuccessTransactionsMachine14f70;
        iExists _;
        cbn;
        rewrite /reg_col;
        iFrame;
        repeat iSplit; try iPureIntro; try reflexivity; try assumption;
          try done | ];
      iExists (tail, suffix, prefix, bytes, remaining, processed,
        transactions, transaction, base, sp, tt)ₗ;
      iFrame "HmachineFinal HarrayFinal HframeFinal";
      rewrite /writeSuccessTransactionsLoadFacts;
      repeat iSplit; try iPureIntro; try assumption; try done
  end.
  Unshelve. all: repeat iIntros "?"; liARun.
Qed.

Lemma write_success_transactions_chunk_14f68
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f70 (writeSuccessTransactionsAt14f70Spec P) -∗
  instr_body 0x14f68 (writeSuccessTransactionsAt14f68Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt14f68Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_chunk_14f68_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hlookup Hcode Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt14f68Block.
  iEval (rewrite /writeSuccessTransactionsMachine14f68) in "Hmachine".
  iDestruct "Hmachine" as "(Hsys & Hother & Hmachine)".
  iDestruct (reg_col_lookup writeSuccessTransactions14f68OtherRegShapes
    6%nat (KindReg "x16", BitsShape 64) with "Hother") as
    (x16 Hx16Shape) "(Hx16 & Hother)".
  { vm_compute. reflexivity. }
  iDestruct (reg_col_lookup
    (delete 6%nat writeSuccessTransactions14f68OtherRegShapes)
    6%nat (KindReg "x17", BitsShape 64) with "Hother") as
    (x17 Hx17Shape) "(Hx17 & Hother)".
  { vm_compute. reflexivity. }
  iDestruct (reg_col_lookup
    (delete 6%nat (delete 6%nat
      writeSuccessTransactions14f68OtherRegShapes))
    3%nat (KindReg "x5", BitsShape 64) with "Hother") as
    (x5 Hx5Shape) "(Hx5 & Hother)".
  { vm_compute. reflexivity. }
  iAssert (writeSuccessTransactionsMachine14f68Block sp base transactions
    processed transaction) with "[Hsys Hother Hmachine Hx16 Hx17 Hx5]"
    as "HblockMachine".
  { rewrite /writeSuccessTransactionsMachine14f68Block.
    iExists x16, x17, x5.
    iFrame.
    repeat iSplit; try iPureIntro; try assumption; try done. }
  iAssert (writeSuccessTransactionsLoadFacts sp base transaction processed
    bytes) as "HfactsFinal".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; try done. }
  iFrame "HblockMachine Harray Hframe HfactsFinal".
  iSplit.
  - iPureIntro. apply write_success_current_unsigned; lia.
  - done.
Qed.
