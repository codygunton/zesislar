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

Lemma s152b_entry_6ae0_output_facts `{!islaG Sigma} `{!threadG}
 (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) :
 decodeItemEntryAt800d6ae0 args locals ⊢
 ⌜length (returnStorage locals) = 40%nat /\
 0 <= decodeItemOutputPointer args /\
 decodeItemOutputPointer args + 40 < RlpDecodeItem.word64Modulus /\
 decodeItemRejectedFacts args /\
 returnStorage locals = decodeItemBeforeStorage args⌝.
Proof.
iIntros "Hentry".
iEval (unfold decodeItemEntryAt800d6ae0) in "Hentry".
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
tauto.
Qed.
