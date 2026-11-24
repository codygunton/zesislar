(* Residual lemmas of the charged decodeItem block +0x0154: the loop-entry
   bound (EntryBound.v), in the three forms a package goal takes (the
   conjunct and its halves). Hand-written, see EntryBound.v. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Lia.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Residuals.decodeItemBudget.EntryBound.
Local Open Scope Z_scope.

(* both *)
Lemma residual_decodeItemBudget_0154_8a6767c6f2507288 (args : DecodeItemArgs) (returnAddress : Z) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  248 <= bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) <= 255 ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) - 247 <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) ->
  0 <= 5 * (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args))
       (bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64 (nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))
          (BV 64 9)) (BV 64 255)) (BV 64 1))) -
     bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (BV 64 1))) + 12 <= 52.
Proof.
  intros Hdomain Hlow Hhigh Hlen.
  replace (BV 64 9) with (Z_to_bv 64 9) by (apply bv_eq; reflexivity).
  pose proof (decodeItemBudgetEntryBound args returnAddress 9 Hdomain ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  lia.
Qed.
#[export] Hint Extern 0 => ZesuSsz.Automation2.ResidualLemmas.zesu_residual_exact constr:(residual_decodeItemBudget_0154_8a6767c6f2507288) : zesu_residual_exact.

(* low *)
Lemma residual_decodeItemBudget_0154_a85c225593b2ca90 (args : DecodeItemArgs) (returnAddress : Z) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  248 <= bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) <= 255 ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) - 247 <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) ->
  0 <= 5 * (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args))
       (bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64 (nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))
          (BV 64 9)) (BV 64 255)) (BV 64 1))) -
     bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (BV 64 1))) + 12.
Proof.
  intros Hdomain Hlow Hhigh Hlen.
  replace (BV 64 9) with (Z_to_bv 64 9) by (apply bv_eq; reflexivity).
  pose proof (decodeItemBudgetEntryBound args returnAddress 9 Hdomain ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  lia.
Qed.
#[export] Hint Extern 0 => ZesuSsz.Automation2.ResidualLemmas.zesu_residual_exact constr:(residual_decodeItemBudget_0154_a85c225593b2ca90) : zesu_residual_exact.

(* high *)
Lemma residual_decodeItemBudget_0154_78c34b00ceeed013 (args : DecodeItemArgs) (returnAddress : Z) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  248 <= bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) <= 255 ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) - 247 <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) ->
  5 * (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args))
       (bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64 (nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))
          (BV 64 9)) (BV 64 255)) (BV 64 1))) -
     bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (BV 64 1))) + 12 <= 52.
Proof.
  intros Hdomain Hlow Hhigh Hlen.
  replace (BV 64 9) with (Z_to_bv 64 9) by (apply bv_eq; reflexivity).
  pose proof (decodeItemBudgetEntryBound args returnAddress 9 Hdomain ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  lia.
Qed.
#[export] Hint Extern 0 => ZesuSsz.Automation2.ResidualLemmas.zesu_residual_exact constr:(residual_decodeItemBudget_0154_78c34b00ceeed013) : zesu_residual_exact.
