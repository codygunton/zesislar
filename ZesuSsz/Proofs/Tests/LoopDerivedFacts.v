Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith.
From lithium Require Import lvar.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Compliance.DecodeItemLoopDerivedFacts.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Open Scope Z_scope.

Lemma loop_registered_successor args n i ps bytes next :
  decodeItemByteFoldFacts args n i ps bytes -> i<n ->
  decodeItemInputBytes args !! Z.to_nat (1+i) = Some next ->
  bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
    (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat (i+1)) bytes)) /\
  decodeItemByteFoldFacts args n (i+1) ps bytes.
Proof.
  intros Hfold Hguard Hlookup.
  zesu_saturate_derived_facts.
  split; zesu_finish_forall_leaf.
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
  zesu_saturate_derived_facts.
  split; zesu_finish_forall_leaf.
Qed.

Lemma loop_registered_terminal_transport args (n i ps : Z) bytes next :
 decodeItemByteFoldFacts args n i ps bytes -> i<n ->
 decodeItemInputBytes args !! Z.to_nat (1+i) = Some next ->
 i+1=n ->
 SimplAnd (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
   (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat n) bytes))) True.
Proof. intros Hfold Hguard Hlookup Hindex. typeclasses eauto. Qed.


Lemma loop_registered_backedge_guard args n i ps bytes :
 decodeItemByteFoldFacts args n i ps bytes ->
 decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
 i<n -> (Z_to_bv 64 (ps+i)+1)%bv <> Z_to_bv 64 (ps+n) -> i+1<n.
Proof.
 intros Hfold Hdomain Hguard Hbranch.
 zesu_saturate_derived_facts. zesu_finish_forall_leaf.
Qed.

Lemma loop_registered_native_spelling args (prefix : bv 8) rest
    (i : lvar "zesuLoopIndex" Z) (next : bv 8) :
 decodeItemByteFoldFacts args
  (@bv_unsigned (MachineWord.Z_idx 8) prefix - 183) i
  (decodeItemInputPointer args + 1)
  (@firstn evm_rlp_types.byte
   (Z.to_nat (@bv_unsigned (MachineWord.Z_idx 8) prefix - 183)) rest) ->
 i < bv_unsigned prefix - 183 ->
 decodeItemInputBytes args !! Z.to_nat (1+i) = Some next ->
 bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i)
  (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest))) ≪ 8)
  (bv_zero_extend 64 next) =
 Z_to_bv 64 (bigEndian (firstn (Z.to_nat (i+1))
  (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest))).
Proof.
 intros Hfold Hguard Hlookup.
 zesu_saturate_derived_facts.
 Fail progress zesu_saturate_derived_facts.
 zesu_finish_forall_leaf.
Qed.
Print Assumptions loop_registered_native_spelling.
