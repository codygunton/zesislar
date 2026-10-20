Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Compliance.DecodeItemLoopDerivedFacts.
Open Scope Z_scope.

Lemma loop_registered_successor args n i ps bytes next :
  decodeItemByteFoldFacts args n i ps bytes -> i<n ->
  decodeItemInputBytes args !! Z.to_nat (1+i) = Some next ->
  bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
    (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat (i+1)) bytes)) /\
  decodeItemByteFoldFacts args n (i+1) ps bytes.
Proof.
  intros Hfold Hguard Hlookup.
  let package := constr:(_ : ZesuDerivedFacts (decodeItemByteFoldFacts args n i ps bytes) _) in
  pose proof (zesu_derived_facts (ZesuDerivedFacts := package) Hfold) as Hderived.
  destruct Hderived as (Hcursor & Hlength & Hbyte & Hacc & Hstep & HnextGuard & Hindex & HterminalAcc & HterminalFold).
  split; [exact (Hacc next Hguard Hlookup) | exact (Hstep next Hguard Hlookup)].
Qed.

Lemma loop_registered_terminal args n i ps bytes next :
  decodeItemByteFoldFacts args n i ps bytes -> i<n ->
  0<=decodeItemInputPointer args ->
  decodeItemInputPointer args + decodeItemInputLength args < word64Modulus ->
  (Z_to_bv 64 (ps+i)+1)%bv = Z_to_bv 64 (ps+n) ->
  decodeItemInputBytes args !! Z.to_nat (1+i) = Some next ->
  bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
    (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat n) bytes)) /\
  decodeItemByteFoldFacts args n n ps bytes.
Proof.
  intros Hfold Hguard Hptr Hend Hbranch Hlookup.
  let package := constr:(_ : ZesuDerivedFacts (decodeItemByteFoldFacts args n i ps bytes) _) in
  pose proof (zesu_derived_facts (ZesuDerivedFacts := package) Hfold) as Hderived.
  destruct Hderived as (Hcursor & Hlength & Hbyte & Hacc & Hstep & HnextGuard & Hindex & HterminalAcc & HterminalFold).
  split.
  - exact (HterminalAcc next Hguard Hptr Hend Hbranch Hlookup).
  - exact (HterminalFold next Hguard Hptr Hend Hbranch Hlookup).
Qed.
