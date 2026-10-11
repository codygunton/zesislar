Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.

Lemma s152b_entry_698c_output_facts `{!islaG Sigma} `{!threadG}
 (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (pointerBytes lengthBytes : list byte) (prefix : byte) (rest : list byte) (isLiteral : bool) :
 decodeItemEntryAt800d698c args locals pointerBytes lengthBytes prefix rest isLiteral ⊢
 ⌜let base := decodeItemOutputPointer args in
 let address := bv_unsigned (bv_add (Z_to_bv 64 base) 24) in
 length (returnStorage locals) = 40%nat /\
 address = Z.add base 24 /\
 Z.of_nat 24 = Z.sub address base /\
 Z.modulo (Z.sub address base) 8 = 0 /\
 Z.of_nat 3 = Z.div (Z.sub address base) 8 /\
 (24 + N.to_nat 8 <= length (returnStorage locals))%nat /\
 length (<[16%nat := Z_to_bv 8 0]> (returnStorage locals)) = 40%nat /\
 (24 + N.to_nat 8 <= length (<[16%nat := Z_to_bv 8 0]> (returnStorage locals)))%nat /\
 (Z.le base address /\ Z.lt address (Z.add base (Z.of_nat (length (<[16%nat := Z_to_bv 8 0]> (returnStorage locals))))))⌝.
Proof.
iIntros "Hentry".
iEval (unfold decodeItemEntryAt800d698c) in "Hentry".
iDestruct "Hentry" as "(Hcore & %Hbranch)".
iEval (unfold decodeItemReturnEntryCore) in "Hcore".
iDestruct "Hcore" as "(Hregs & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H2 & H1 & H8 & Hin & Hout & Hstack & %Hfacts & Hcaller & _)".
iPureIntro.
destruct Hfacts as (Hdomain & Hframe & Hstorage).
assert (Hbase : 0 <= decodeItemOutputPointer args).
{ unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed,
 RlpDecodeItem.decodeItemEntryLayout in Hdomain. tauto. }
assert (Hnowrap : decodeItemOutputPointer args + 40 < RlpDecodeItem.word64Modulus).
{ unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed,
 RlpDecodeItem.decodeItemEntryLayout in Hdomain. tauto. }
cbn zeta.
assert (Hbounds : 0 <= decodeItemOutputPointer args + 24 < bv_modulus 64).
{ unfold RlpDecodeItem.word64Modulus in Hnowrap. unfold bv_modulus. cbn. lia. }
replace (bv_add (Z_to_bv 64 (decodeItemOutputPointer args)) 24)
 with (Z_to_bv 64 (decodeItemOutputPointer args + 24)) by bv_solve.
rewrite (Z_to_bv_small 64 _ Hbounds).
replace (decodeItemOutputPointer args + 24 - decodeItemOutputPointer args) with 24 by lia.
rewrite !length_insert Hstorage. cbn. repeat split; lia.
Qed.
