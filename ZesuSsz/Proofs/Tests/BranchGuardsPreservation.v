Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From stdpp Require Import bitvector.definitions.
From lithium Require Import simpl_classes.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Open Scope Z_scope.
Lemma branch_guard_preserve_original_guard (word limit : bv 64) :
  129 <= bv_unsigned word <= 183 ->
  bv_signed (bv_zero_extend 128 (bv_and word 127)) >=
    bv_signed (bv_zero_extend 128 limit) -> True.
Proof.
  intros Hrange Hguard.
  let original := type of Hguard in
  ZesuSsz.Automation2.PureFacts.zesu_saturate_derived_facts;
  let retained := type of Hguard in constr_eq original retained.
  match goal with Hnormalized : bv_unsigned word - 128 >= bv_unsigned limit |- _ => idtac end.
  Fail progress ZesuSsz.Automation2.PureFacts.zesu_saturate_derived_facts.
  exact I.
Qed.
Lemma branch_guard_preserve_refused_guard (word mask : bv 64) :
  bv_unsigned (bv_and word mask) = 0 -> True.
Proof.
  intro Hguard. evar (pending : bv 64).
  let hole := eval unfold pending in pending in is_evar hole.
  Fail progress ZesuSsz.Automation2.PureFacts.zesu_saturate_derived_facts.
  let retained := type of Hguard in
  constr_eq retained constr:(bv_unsigned (bv_and word mask) = 0).
  let hole := eval unfold pending in pending in is_evar hole.
  let hole := eval unfold pending in pending in unify hole (Z_to_bv 64 0).
  exact I.
Qed.
(* The class guard of the generated 6a24 loop entry: saturation keeps the
   original guard, so a consumer that reads the guard as written still finds it. *)
Lemma branch_guard_preserve_loop_class0_guard args :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  bv_signed (BV 128 183) < bv_signed (bv_zero_extend 128 (bv_and
    (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))) ->
  bv_signed (BV 128 183) < bv_signed (bv_zero_extend 128 (bv_and
    (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))).
Proof.
  intros Hdomain Hguard.
  let original := type of Hguard in
  ZesuSsz.Automation2.PureFacts.zesu_saturate_derived_facts;
  let retained := type of Hguard in constr_eq original retained.
  match goal with Hnormalized :
    183 < bv_unsigned (List.nth 0 (decodeItemInputBytes args) _) |- _ => idtac end.
  Fail progress ZesuSsz.Automation2.PureFacts.zesu_saturate_derived_facts.
  assumption.
Qed.
Print Assumptions branch_guard_preserve_original_guard.
Print Assumptions branch_guard_preserve_refused_guard.
Print Assumptions branch_guard_preserve_loop_class0_guard.

Lemma branch_guard_preserve_derived_input_evar (word : bv 64) : True.
Proof.
  evar (unknown : bv 64).
  evar (normalized : Prop).
  let hole := eval unfold unknown in unknown in is_evar hole.
  let hole := eval unfold normalized in normalized in is_evar hole.
  Fail assert (ZesuSsz.Automation.PureFacts.ZesuDerivedFacts
    (bv_unsigned (bv_and unknown 127) = 0) normalized)
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
  Fail assert (ZesuSsz.Automation.PureFacts.ZesuDerivedFacts
    (bv_unsigned (bv_and word mask) = 0) normalized)
    by typeclasses eauto.
  let hole := eval unfold normalized in normalized in is_evar hole.
  let hole := eval unfold normalized in normalized in unify hole True.
  exact I.
Qed.
Print Assumptions branch_guard_preserve_derived_input_evar.
Print Assumptions branch_guard_preserve_derived_output_evar.
