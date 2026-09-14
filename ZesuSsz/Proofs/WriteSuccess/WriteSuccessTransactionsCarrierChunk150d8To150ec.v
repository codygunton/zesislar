Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState150d8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState150ec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Definition writeSuccessTransactionsAt150d8CarrierBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (writeSuccessTransactionsMachine150d8Carrier
      sp base transactions processed transaction
      first second third fourth items ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt150d8CarrierBlock) := I.

Lemma write_success_transactions_carrier_chunk_150d8_to_150ec_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (HtransactionLength : length (writeSuccessTransactionBytes transaction) = 288%nat)
    (HbaseAlign : (base + 288 * Z.of_nat (length processed)) `mod` 8 = 0)
    (HbaseLower : (mapRamBase defaultMap) <= base + 288 * Z.of_nat (length processed))
    (HbaseUpper : base + 288 * Z.of_nat (length processed) + 288 < (machineRamEnd defaultMap))
    (HspAlign8 : bv_unsigned sp `mod` 8 = 0)
    (HspLower48 : (mapRamBase defaultMap) <= bv_unsigned sp - 48)
    (HspUpper1896 : bv_unsigned sp + 1896 < (machineRamEnd defaultMap)) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150ec (writeSuccessTransactionsAt150ecCarrierSpec P) -∗
  instr_body 0x150d8 (writeSuccessTransactionsAt150d8CarrierBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  rewrite /writeSuccessTransactionsAt150d8CarrierBlock.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  all: destruct H0 as
    (HitemsLength & HitemsBound & HfirstAlign & HfirstLower & HfirstUpper &
      HspAlign & HspLower & HspUpper).
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  iExists (items, fourth, third, second, first, tail, suffix, prefix, bytes,
    remaining, processed, transactions, transaction, base, sp, tt)ₗ.
  zesu_block.
  iFrame "∗".
  zesu_promote_folded_pure_resources.
  iEval (unfold writeSuccessTransactionsLoadFacts).
  zesu_finish_pure_resources.
Qed.

Lemma write_success_transactions_carrier_chunk_150d8_to_150ec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150ec (writeSuccessTransactionsAt150ecCarrierSpec P) -∗
  instr_body 0x150d8 (writeSuccessTransactionsAt150d8CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt150d8CarrierSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail first second third fourth items)
    "(Hmachine & Harray & Hphase & HloadFacts & _)".
  iEval (unfold writeSuccessTransactionsLoadFacts) in "HloadFacts".
  iDestruct "HloadFacts" as
    "(%HtransactionLength & %HbaseAlign & %HbaseLower & %HbaseUpper &
      %HspAlign8 & %HspLower48 & %HspUpper1896 & _)".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof
    (write_success_transactions_carrier_chunk_150d8_to_150ec_raw P sp base
      transaction transactions processed remaining bytes prefix suffix tail
      first second third fourth items HtransactionLength HbaseAlign
      HbaseLower HbaseUpper HspAlign8 HspLower48 HspUpper1896 with
      "Hlookup Hcode Hnext") as "Hraw".
  iEval (rewrite instr_pre'_eq) in "Hraw".
  iApply "Hraw".
  rewrite /writeSuccessTransactionsAt150d8CarrierBlock.
  iFrame.
Qed.
