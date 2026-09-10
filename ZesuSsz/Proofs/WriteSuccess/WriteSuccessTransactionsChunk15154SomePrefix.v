Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15154Frame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSomeHandoff.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_1515c_offset (sp : bv 64) :
  (bv_unsigned sp + 1896 < 0x40000000)%Z ->
  bv_unsigned (sp + BV 64 1656)%bv = bv_unsigned sp + 1656.
Proof.
  intro Hupper. apply bv_unsigned_add_no_wrap_64.
  rewrite bv_unsigned_BV.
  pose proof (bv_unsigned_in_range 64 sp) as Hrange.
  unfold bv_modulus in Hrange. cbn in Hrange. lia.
Qed.

Lemma write_success_transactions_chunk_1515c_alignment (sp : bv 64) :
  bv_unsigned sp `mod` 16 = 0 ->
  (bv_unsigned sp + 1896 < 0x40000000)%Z ->
  bv_extract 0 2 (sp + BV 64 1656)%bv = BV 2 0.
Proof.
  intros Halign Hupper. apply bv_eq.
  rewrite bv_extract_0_unsigned.
  rewrite (write_success_transactions_chunk_1515c_offset sp Hupper).
  rewrite !bv_unsigned_BV. unfold bv_wrap, bv_modulus. cbn.
  rewrite Z.add_mod; try lia.
Qed.

Lemma write_success_transactions_chunk_1515c_ram_limit :
  bv_unsigned
    (BV 64 536870912 + BV 64 536870912 - BV 64 4)%bv = 1073741820.
Proof. vm_compute. reflexivity. Qed.

Lemma write_success_transactions_chunk_1515c_lower (sp : bv 64) :
  (0x20000000 <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned sp + 1896 < 0x40000000)%Z ->
  bv_unsigned (sp + BV 64 1656)%bv >= bv_unsigned (BV 64 536870912).
Proof.
  intros Hlower Hupper.
  rewrite (write_success_transactions_chunk_1515c_offset sp Hupper).
  rewrite bv_unsigned_BV. lia.
Qed.

Lemma write_success_transactions_chunk_1515c_upper (sp : bv 64) :
  (bv_unsigned sp + 1896 < 0x40000000)%Z ->
  bv_unsigned (sp + BV 64 1656)%bv <=
    bv_unsigned (BV 64 536870912 + BV 64 536870912 - BV 64 4).
Proof.
  intro Hupper.
  rewrite (write_success_transactions_chunk_1515c_offset sp Hupper).
  rewrite write_success_transactions_chunk_1515c_ram_limit.
  lia.
Qed.

Lemma write_success_transactions_chunk_1515c_to_15168
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15168
    (writeSuccessTransactionsOptionalAddressSomeAt15168Spec P) -∗
  instr_body 0x1515c
    (writeSuccessTransactionsOptionalAddressSomeAt1515cSpec P).
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
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try liARun.
  all: iIntros "HdataOwn".
  all: iIntros "HtransactionTail".
  all: iIntros "HremainingTail".
  all: iDestruct "HtransactionTail" as "(HaccessOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as
    "(HaccessEntriesOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(HblobOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(HauthOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(%Hvalid & _)".
  all: iDestruct "HremainingTail" as "(Hremaining & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Hmmio & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Htrace & HremainingTail)".
  all: iDestruct "HremainingTail" as "(HP & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Hinv & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Hloop & _)".
  iDestruct (persistent with "Hinv") as "#HinvPersistent".
  iPoseProof "HinvPersistent" as "#HinvCopy".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant)
    in "HinvCopy".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[_ HinvCopy]".
  iDestruct "HinvCopy" as "[HspAlign HinvCopy]".
  iDestruct "HinvCopy" as "[HspLower HinvCopy]".
  iDestruct "HinvCopy" as "[HspUpper HinvCopy]".
  iDestruct "HspAlign" as "%HspAlign".
  iDestruct "HspLower" as "%HspLower".
  iDestruct "HspUpper" as "%HspUpper".
  have HspAlign8 : bv_unsigned sp `mod` 8 = 0.
  { apply Z.mod_divide; [lia|].
    apply Z.mod_divide in HspAlign; [|lia].
    destruct HspAlign as [factor Hfactor].
    exists (2 * factor). lia. }
  have Hlower1640 : (0x20000000 <= bv_unsigned sp + 1640)%Z by lia.
  have Hupper1640 : (bv_unsigned sp + 1640 < 0x40000000)%Z by lia.
  have Hlower1648 : (0x20000000 <= bv_unsigned sp + 1648)%Z by lia.
  have Hupper1648 : (bv_unsigned sp + 1648 < 0x40000000)%Z by lia.
  have Hlower1656 : (0x20000000 <= bv_unsigned sp + 1656)%Z by lia.
  have Hupper1656 : (bv_unsigned sp + 1656 < 0x40000000)%Z by lia.
  all: liARun.
  Unshelve. all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; rewrite !bv_unsigned_BV;
    exact H1).
  all: try (apply write_success_transactions_chunk_1515c_alignment;
    assumption).
  all: try (apply write_success_transactions_chunk_1515c_lower;
    assumption).
  all: try (apply write_success_transactions_chunk_1515c_upper;
    assumption).
  Unshelve.
  iRename select (bv_unsigned LET0 ↦ₘ _)%I into "Hmem1656".
  subst LET0.
  iAssert ((bv_unsigned sp + 1656) ↦ₘ _)%I with "[Hmem1656]" as
    "Hmem1656Target".
  { rewrite <- (write_success_transactions_chunk_1515c_offset sp HspUpper).
    iExact "Hmem1656". }
  iRename select (base ↦ₘ∗ prefix)%I into "Hprefix".
  iRename select ((base + 288 * length processed) ↦ₘ∗ suffix)%I into "Hsuffix".
  iRename select
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn processed)%I
    into "Hprocessed".
  iAssert (writeSuccessTransactionsMachine15168
    sp base transactions processed transaction)%I with
    "[-Hprefix Hsuffix Hprocessed HdataOwn HaccessOwn HaccessEntriesOwn HblobOwn
       HauthOwn Hremaining Hmmio Htrace HP HinvPersistent Hloop]" as "Hmachine".
  { iEval (unfold writeSuccessTransactionsMachine15168,
      WriteSuccessTransactionsBoundary150e8.writeSuccessTransactionsScratch150e8).
    iFrame. }
  iAssert (WriteSuccessTransactionsSpec.writeSuccessTransactionOwn transaction)%I
    with "[HdataOwn HaccessOwn HaccessEntriesOwn HblobOwn HauthOwn]"
    as "HtransactionOwn".
  { iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionOwn).
    iFrame. iPureIntro. split; [exact Hvalid|trivial]. }
  iAssert (writeSuccessTransactions15168Frame P sp base transaction
    transactions processed remaining bytes prefix suffix tail)%I
    with "[Hprefix Hsuffix Hprocessed HtransactionOwn Hremaining Hmmio Htrace
      HP HinvPersistent Hloop]"
    as "Hframe".
  { iEval (unfold writeSuccessTransactions15168Frame). iFrame.
    iExact "HinvPersistent". }
  iAssert (⌜WriteSuccessTransactionsSpec.writeSuccessTransactionByte
    transaction 285 ≠ BV 8 0⌝)%I as "Hnonzero".
  { iPureIntro. exact H0. }
  iPoseProof (write_success_transactions_chunk_15168_pack P sp base transaction
    transactions processed remaining bytes prefix suffix tail
    with "Hnonzero Hmachine Hframe") as "Hsome".
  iDestruct "Hsome" as
    (sp' base' transaction' transactions' processed' remaining' bytes' prefix'
      suffix' tail') "[Hnonzero' Hhandoff]".
  iExists (tail', suffix', prefix', bytes', remaining', processed', transactions',
    transaction', base', sp', tt)ₗ.
  iSplitL "Hnonzero'". { iExact "Hnonzero'". }
  iExact "Hhandoff".
Qed.
