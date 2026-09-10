From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.

Definition writeSuccessBlobHashesSegment02State
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessBlobHashesOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x19" ↦ᵣ RVal_Bits pointer ∗
   "x22" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessBlobHashesScratch sp ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessBlobHashesEvents sp (S remaining) tail) ∗ P ∗
   writeSuccessFixedWidthArrayInvariant
     sp pointer base total processed remaining bytes ∗
   instr_pre 0x15564
     (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesSegment02State) := I.

Lemma write_success_blob_hashes_region_start_18
    (pointer : bv 64) (base : Z) (processed : nat) :
  bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z ->
  IslarisMemory.array_region_start 8 base (bv_unsigned pointer + 18) =
    (32 * processed + 18)%nat.
Proof.
  intros Hpointer.
  rewrite /IslarisMemory.array_region_start Hpointer.
  change (Z.to_nat ((base + 32 * Z.of_nat processed + 18 - base) / 1) =
    (32 * processed + 18)%nat).
  rewrite Z.div_1_r.
  lia.
Qed.

Lemma write_success_blob_hashes_take_18
    (bytes : list (bv 8)) (processed remaining : nat) :
  length bytes = (32 * (processed + S remaining))%nat ->
  take 1 (drop (32 * processed + 18) bytes) =
    [default (BV 8 0) (bytes !! (32 * processed + 18)%nat)].
Proof.
  intros Hlength.
  have Hindex : (32 * processed + 18 < length bytes)%nat by lia.
  destruct (bytes !! (32 * processed + 18)%nat) eqn:Hlookup.
  - have Hdrop : (drop (32 * processed + 18) bytes) !! 0%nat = Some b.
    { rewrite lookup_drop.
      replace (32 * processed + 18 + 0)%nat with
        (32 * processed + 18)%nat by lia.
      exact Hlookup. }
    pose proof (take_S_r (drop (32 * processed + 18) bytes) 0 b Hdrop)
      as Htake.
    cbn in Htake. exact Htake.
  - apply lookup_ge_None in Hlookup. lia.
Qed.

Lemma write_success_blob_hashes_segment02_state_intro
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) :
  writeSuccessBlobHashesSegment02State P sp pointer base total processed
    remaining bytes tail -∗ writeSuccessBlobHashesLoopSpec P.
Proof.
  iIntros "Hstate".
  rewrite /writeSuccessBlobHashesLoopSpec.
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iExact "Hstate".
Qed.
