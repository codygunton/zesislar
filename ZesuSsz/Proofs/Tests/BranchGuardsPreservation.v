Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.Switches.BranchGuards.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import EvmSailRlp.evm_rlp_types.
From stdpp Require Import bitvector.definitions.
From lithium Require Import simpl_classes.
Require Import isla.riscv64.riscv64.
Open Scope Z_scope.
Lemma branch_guard_preserve_original_guard (word limit : bv 64) :
  129 <= bv_unsigned word <= 183 ->
  bv_signed (bv_zero_extend 128 (bv_and word 127)) >=
    bv_signed (bv_zero_extend 128 limit) -> True.
Proof.
  intros Hrange Hguard.
  let original := type of Hguard in
  zesu_saturate_derived_facts;
  let retained := type of Hguard in constr_eq original retained.
  match goal with Hnormalized : bv_unsigned word - 128 >= bv_unsigned limit |- _ => idtac end.
  Fail progress zesu_saturate_derived_facts.
  exact I.
Qed.
Lemma branch_guard_preserve_refused_guard (word mask : bv 64) :
  bv_unsigned (bv_and word mask) = 0 -> True.
Proof.
  intro Hguard. evar (pending : bv 64).
  let hole := eval unfold pending in pending in is_evar hole.
  Fail progress zesu_saturate_derived_facts.
  let retained := type of Hguard in
  constr_eq retained constr:(bv_unsigned (bv_and word mask) = 0).
  let hole := eval unfold pending in pending in is_evar hole.
  let hole := eval unfold pending in pending in unify hole (Z_to_bv 64 0).
  exact I.
Qed.
Lemma branch_guard_preserve_short_list_old_consumer args (prefix : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args inputPrefix rest ->
  192 <= bv_unsigned inputPrefix <= 247 ->
  bv_unsigned prefix = bv_unsigned inputPrefix ->
  bv_signed (bv_zero_extend 128 (bv_and (prefix + 64) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hhead Hclass Hvalue Hguard. destruct Hclass as [Hlower Hupper].
  let original := type of Hguard in
  zesu_saturate_derived_facts;
  let retained := type of Hguard in constr_eq original retained.
  let witness := constr:(_ : SimplAnd (decodeItemRejectedFacts args) True) in
  lazymatch witness with
  | context [decodeItemShortListGuardRejected] => exact ((proj1 witness) I)
  end.
Qed.
Lemma branch_guard_preserve_short_string_old_consumer args (prefix : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args inputPrefix rest ->
  129 <= bv_unsigned inputPrefix <= 183 ->
  bv_unsigned prefix = bv_unsigned inputPrefix ->
  ~ bv_signed (bv_zero_extend 128 (bv_and prefix 127)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  decodeItemAcceptedFacts args false 1 (bv_unsigned inputPrefix - 128).
Proof.
  intros Hdomain Hhead Hclass Hvalue Hguard. destruct Hclass as [Hlower Hupper].
  let original := type of Hguard in
  zesu_saturate_derived_facts;
  let retained := type of Hguard in constr_eq original retained.
  let witness := constr:(_ : SimplAnd
    (decodeItemAcceptedFacts args false 1 (bv_unsigned inputPrefix - 128)) True) in
  lazymatch witness with
  | context [decodeItemShortStringGuardAccepted] => exact ((proj1 witness) I)
  end.
Qed.
Print Assumptions branch_guard_preserve_original_guard.
Print Assumptions branch_guard_preserve_refused_guard.
Print Assumptions branch_guard_preserve_short_list_old_consumer.
Print Assumptions branch_guard_preserve_short_string_old_consumer.

Lemma branch_guard_preserve_derived_input_evar (word : bv 64) : True.
Proof.
  evar (unknown : bv 64).
  evar (normalized : Prop).
  let hole := eval unfold unknown in unknown in is_evar hole.
  let hole := eval unfold normalized in normalized in is_evar hole.
  Fail assert (ZesuDerivedFacts (bv_unsigned (bv_and unknown 127) = 0) normalized)
    by typeclasses eauto.
  let hole := eval unfold unknown in unknown in is_evar hole.
  let hole := eval unfold normalized in normalized in is_evar hole.
  let hole := eval unfold unknown in unknown in unify hole word.
  let hole := eval unfold normalized in normalized in unify hole True.
  exact I.
Qed.
Lemma branch_guard_preserve_derived_output_evar (word mask : bv 64) : True.
Proof.
  evar (normalized : Prop).
  let hole := eval unfold normalized in normalized in is_evar hole.
  Fail assert (ZesuDerivedFacts (bv_unsigned (bv_and word mask) = 0) normalized)
    by typeclasses eauto.
  let hole := eval unfold normalized in normalized in is_evar hole.
  let hole := eval unfold normalized in normalized in unify hole True.
  exact I.
Qed.
Print Assumptions branch_guard_preserve_derived_input_evar.
Print Assumptions branch_guard_preserve_derived_output_evar.
