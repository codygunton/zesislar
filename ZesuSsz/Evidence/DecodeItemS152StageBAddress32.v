Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.

Lemma s152_stageB_address32 (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) :
 decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
 length (returnStorage locals) = 40%nat ->
 let address := bv_add (Z_to_bv 64 (decodeItemOutputPointer args)) (Z_to_bv 64 32) in
 bv_unsigned address = Z.add (decodeItemOutputPointer args) 32 /\
 Z.of_nat 32 = Z.sub (bv_unsigned address) (decodeItemOutputPointer args) /\
 (32 + N.to_nat 8 <= length (returnStorage locals))%nat /\
 Z.modulo (Z.sub (bv_unsigned address) (decodeItemOutputPointer args)) 8 = 0 /\
 Z.of_nat 4 = Z.div (Z.sub (bv_unsigned address) (decodeItemOutputPointer args)) 8.
Proof.
intros Hdomain Hstorage.
assert (Hbase : 0 <= decodeItemOutputPointer args).
{ unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed,
 RlpDecodeItem.decodeItemEntryLayout in Hdomain. tauto. }
assert (Hnowrap : decodeItemOutputPointer args + 40 < RlpDecodeItem.word64Modulus).
{ unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed,
 RlpDecodeItem.decodeItemEntryLayout in Hdomain. tauto. }
cbn zeta.
assert (Hbounds : 0 <= decodeItemOutputPointer args + 32 < bv_modulus 64).
{ unfold RlpDecodeItem.word64Modulus in Hnowrap. unfold bv_modulus. cbn. lia. }
replace (bv_add (Z_to_bv 64 (decodeItemOutputPointer args)) (Z_to_bv 64 32))
 with (Z_to_bv 64 (decodeItemOutputPointer args + 32)) by bv_solve.
rewrite (Z_to_bv_small 64 _ Hbounds).
replace (decodeItemOutputPointer args + 32 - decodeItemOutputPointer args) with 32 by lia.
rewrite Hstorage. cbn. repeat split; lia.
Qed.
