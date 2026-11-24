(* Residual lemmas of the charged decodeItem block +0x00b4: the loop-entry
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
Lemma residual_decodeItemBudget_00b4_fadd5f936bb35754 (args : DecodeItemArgs) (returnAddress : Z) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  184 <= bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) <= 191 ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) - 183 <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) ->
  0 <= 5 * (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args))
       (bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64 (nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))
          (BV 64 73)) (BV 64 255)) (BV 64 1))) -
     bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (BV 64 1))) + 12 <= 52.
Proof.
  intros Hdomain Hlow Hhigh Hlen.
  replace (BV 64 73) with (Z_to_bv 64 73) by (apply bv_eq; reflexivity).
  pose proof (decodeItemBudgetEntryBound args returnAddress 73 Hdomain ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  lia.
Qed.
#[export] Hint Extern 0 => ZesuSsz.Automation2.ResidualLemmas.zesu_residual_exact constr:(residual_decodeItemBudget_00b4_fadd5f936bb35754) : zesu_residual_exact.

(* low *)
Lemma residual_decodeItemBudget_00b4_d988f2d4bd2f19c6 (args : DecodeItemArgs) (returnAddress : Z) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  184 <= bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) <= 191 ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) - 183 <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) ->
  0 <= 5 * (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args))
       (bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64 (nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))
          (BV 64 73)) (BV 64 255)) (BV 64 1))) -
     bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (BV 64 1))) + 12.
Proof.
  intros Hdomain Hlow Hhigh Hlen.
  replace (BV 64 73) with (Z_to_bv 64 73) by (apply bv_eq; reflexivity).
  pose proof (decodeItemBudgetEntryBound args returnAddress 73 Hdomain ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  lia.
Qed.
#[export] Hint Extern 0 => ZesuSsz.Automation2.ResidualLemmas.zesu_residual_exact constr:(residual_decodeItemBudget_00b4_d988f2d4bd2f19c6) : zesu_residual_exact.

(* high *)
Lemma residual_decodeItemBudget_00b4_1eb91c90e1719640 (args : DecodeItemArgs) (returnAddress : Z) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  184 <= bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) <= 191 ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) - 183 <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) ->
  5 * (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args))
       (bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64 (nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))
          (BV 64 73)) (BV 64 255)) (BV 64 1))) -
     bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (BV 64 1))) + 12 <= 52.
Proof.
  intros Hdomain Hlow Hhigh Hlen.
  replace (BV 64 73) with (Z_to_bv 64 73) by (apply bv_eq; reflexivity).
  pose proof (decodeItemBudgetEntryBound args returnAddress 73 Hdomain ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  lia.
Qed.
#[export] Hint Extern 0 => ZesuSsz.Automation2.ResidualLemmas.zesu_residual_exact constr:(residual_decodeItemBudget_00b4_1eb91c90e1719640) : zesu_residual_exact.
