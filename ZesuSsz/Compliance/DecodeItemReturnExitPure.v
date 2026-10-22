Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.DecodeItemPathAgreement.
Import ListNotations.
Open Scope Z_scope.

(* Each lemma connects an exact Q44 byte image to the Q45 path fact.
   Machine ownership and writes at these PCs remain block obligations. *)


Lemma returnExitEmptyString args prefix rest pointerBytes lengthBytes consumedBytes :
  decodeItemInputBytes args = prefix :: rest ->
  decodeItemC1BDomain args ->
  bv_unsigned prefix = 128 ->
  (length (decodeItemBeforeStorage args) = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = 1 ->
  littleEndian lengthBytes = 0 ->
  littleEndian consumedBytes = 1 mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateSuccess false 1 0 ->
  decodeItemSailSuccess args false 1 0 ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
       pointerBytes lengthBytes consumedBytes false).
Proof.
  intros Hinput Hdomain Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv Hcandidate Hsail.
  eapply decodeItemEmptyStringReturn; [exact Hdomain|exact Hcandidate| |exact Hsail].
  rewrite Hinput. eapply return_800d69d4_emptyString; eauto.
Qed.
