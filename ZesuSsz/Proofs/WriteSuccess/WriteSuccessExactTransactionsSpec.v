Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.Resources.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncodeFragments.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTrace.

Import ListNotations.

Definition writeSuccessExactTransactionsPayloads
    (transactions : list writeSuccessTransaction) : list (list (bv 8)) :=
  map writeSuccessPrivateBytes
    (concat (map writeSuccessTransactionFragments
      (map writeSuccessTransactionObservationOfNative transactions))).

Definition writeSuccessExactTransactionsEvents (sp : bv 64)
    (transactions : list writeSuccessTransaction) (tail : spec) : spec :=
  writeOutputPayloadsSpec (writeSuccessTransactionsDescriptors sp transactions)
    (writeSuccessExactTransactionsPayloads transactions) tail.

Lemma writeSuccessExactTransactionsPayloads_length sp transactions :
  length (writeSuccessTransactionsDescriptors sp transactions) =
  length (writeSuccessExactTransactionsPayloads transactions).
Proof.
  unfold writeSuccessExactTransactionsPayloads. rewrite map_length.
  apply writeSuccessTransactionsDescriptors_fragments_length.
Qed.

Lemma writeSuccessExactTransactionsEvents_app sp left right tail :
  writeSuccessExactTransactionsEvents sp (left ++ right) tail =
  writeSuccessExactTransactionsEvents sp left
    (writeSuccessExactTransactionsEvents sp right tail).
Proof.
  unfold writeSuccessExactTransactionsEvents,
    writeSuccessExactTransactionsPayloads.
  have Hdescriptors : writeSuccessTransactionsDescriptors sp (left ++ right) =
      writeSuccessTransactionsDescriptors sp left ++
      writeSuccessTransactionsDescriptors sp right.
  { induction left; simpl; [reflexivity|rewrite IHleft app_assoc; reflexivity]. }
  rewrite Hdescriptors !map_app concat_app map_app.
  apply writeOutputPayloadsSpec_app.
  rewrite map_length. apply writeSuccessTransactionsDescriptors_fragments_length.
Qed.

(** The loop retains the complete input arrays. The cursor changes only the
    pure remaining list and the exact observable trace continuation. *)
Definition writeSuccessExactTransactionsState `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length processed))) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
   writeSuccessTransactionsScratch sp base (length transactions) ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactTransactionsEvents sp remaining tail) ∗
   ⌜transactions = processed ++ remaining⌝ ∗
   ⌜bytes = writeSuccessTransactionsBytes transactions⌝ ∗
   ⌜length bytes = (288 * length transactions)%nat⌝ ∗
   ⌜(length transactions < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   ⌜base `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessExactTransactionsState) := I.

Lemma writeSuccessTransactionCursor_complete
    (transactions processed remaining : list writeSuccessTransaction) :
  transactions = processed ++ remaining ->
  (length transactions < 2 ^ 64)%nat ->
  Z_to_bv 64 (Z.of_nat (length processed)) =
    Z_to_bv 64 (Z.of_nat (length transactions)) <-> remaining = [].
Proof.
  intros -> Hbound. rewrite app_length in Hbound |- *.
  split.
  - intros Heq.
    apply Nat2Z.inj_lt in Hbound.
    rewrite Nat2Z.inj_pow in Hbound. cbn in Hbound.
    apply (f_equal bv_unsigned) in Heq.
    rewrite !Z_to_bv_unsigned !bv_wrap_small in Heq;
      try (unfold bv_modulus; cbn; lia).
    have Hlength : length remaining = 0%nat by lia.
    apply nil_length_inv. exact Hlength.
  - intros ->. simpl. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma writeSuccessExactTransactionsState_exit `{!islaG Sigma} `{!threadG}
    sp base transactions bytes tail P :
  writeSuccessExactTransactionsState sp base transactions transactions []
    bytes tail P -∗
  writeSuccessTransactionsLoopExit sp base transactions bytes tail P.
Proof.
  iIntros "Hstate".
  rewrite /writeSuccessExactTransactionsState /writeSuccessTransactionsLoopExit
    /writeSuccessTransactionsScratch
    /writeSuccessExactTransactionsEvents /writeSuccessExactTransactionsPayloads /=.
  zesu_open_resource_groups. zesu_run.
Qed.

Print Assumptions writeSuccessExactTransactionsPayloads_length.
Print Assumptions writeSuccessExactTransactionsEvents_app.
Print Assumptions writeSuccessExactTransactionsState_exit.
Print Assumptions writeSuccessTransactionCursor_complete.
