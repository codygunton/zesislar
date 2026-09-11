Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f28.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f2c.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_14f28_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

#[local] Hint Rewrite write_success_14f28_current_unsigned using lia :
  lithium_rewrite.

Definition writeSuccessTransactionsAt14f28Block
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
   "x23" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactions14f2cFrame sp base transactions processed ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14f28Block) := I.

Lemma write_success_transactions_chunk_14f28_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f2c (writeSuccessTransactionsAt14f2cSpec P) -∗
  instr_body 0x14f28 (writeSuccessTransactionsAt14f28Block P sp base
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
  all: rewrite ?write_success_14f28_current_unsigned; try lia.
  all: try (iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24,
      tt)ₗ).
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_14f28_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  iIntros "Hprefix24 Hsuffix32".
  cbn.
  have Hstart :
    Z.to_nat
      (bv_unsigned (Z_to_bv 64
        (base + 288 * Z.of_nat (length processed))) + 24 -
       (base + 288 * Z.of_nat (length processed))) = 24%nat.
  { rewrite H7. lia. }
  iEval (rewrite Hstart) in "Hprefix24 Hsuffix32".
  rewrite Hstart.
  iEval (cbn) in "Hsuffix32".
  rewrite H7 !Z.add_0_r.
  iFrame "Hprefix24 Hsuffix32".
  repeat iSplit; try iPureIntro; try lia; try done.
  liARun.
  iExists (tail, suffix, prefix, bytes, remaining, transactions, sp, tt)ₗ.
  iFrame.
  repeat iSplit; try (iPureIntro; assumption).
  all: try done.
Qed.

Lemma write_success_transactions_chunk_14f28
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f2c (writeSuccessTransactionsAt14f2cSpec P) -∗
  instr_body 0x14f28 (writeSuccessTransactionsAt14f28Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt14f28Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hsys & Hx25 & Hx24 & Hx9 & Hx10 & Hprefix & Hword16 & Hsuffix24 &
      Hempty24 & Hmachine & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (unfold writeSuccessTransactions14f28Frame) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hstack0 & Hstack1 & Hstack2 & Hstack3 & Hstack4 & Hstack5 &
      Hx2 & Hx11 & Hother & _)".
  iDestruct (reg_col_lookup
    (delete 7%nat
      (delete 20%nat writeSuccessTransactions14f1cOtherRegShapes))
    18%nat (KindReg "x23", BitsShape 64) with "Hother") as
    (x23 Hx23Shape) "(Hx23 & Hother)".
  { vm_compute. reflexivity. }
  iAssert (writeSuccessTransactions14f2cFrame sp base transactions processed)
    with "[Hstack0 Hstack1 Hstack2 Hstack3 Hstack4 Hstack5 Hx2 Hx11 Hother]"
    as "Hmachine".
  { rewrite /writeSuccessTransactions14f2cFrame. iFrame. }
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    16
    (base + 288 * Z.of_nat (length processed) + 24)
    (base + 288 * Z.of_nat (length processed) + 16) with
    "Hprefix Hsuffix24 Hword16 [] [] []") as "Harray".
  { iPureIntro. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite Hlength. lia. }
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_chunk_14f28_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hlookup Hcode Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt14f28Block.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_14f28_current_unsigned; try lia.
  all: try iFrame.
  all: try done.
Qed.
