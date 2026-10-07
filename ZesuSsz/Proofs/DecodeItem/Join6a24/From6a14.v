Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.InstructionLookup.
Require Import ZesuSsz.Automation.Switches.RamFault.
Require Import ZesuSsz.Automation.Switches.EvarSideconditionGuard.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldInitializationWitnesses.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
Require Import ZesuSsz.Compliance.DecodeItemInitializationPureFacts.
Open Scope Z_scope.

Lemma decodeItemInitialization6a14Native_correct `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte) (oldAcc oldCursor loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  instr_pre 0x800d6a24
    (∃ (successor_inputPrefix : byte) (successor_rest : list byte),
       decodeItemEntryAt800d6a24 args successor_inputPrefix successor_rest)%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a14
    (decodeItemEntryAt800d6a14 args n payloadStart lengthBytes frameBytes
       oldAcc oldCursor loaded inputPrefix rest ∗ True)%I.
Proof.
iIntros "Hhandoff Hcode".
iEval (unfold decodeItemSelectedCode) in "Hcode".
iDestruct "Hcode" as "#Hcode".
zesu_block.
iExists (rest, inputPrefix, tt)ₗ.
cbn.
match goal with Hdomain : decodeItemC1BDomain args |- _ => rename Hdomain into HdomainFacts end.
match goal with Hprovenance : decodeItemFoldProvenance args false inputPrefix rest n payloadStart lengthBytes |- _ => rename Hprovenance into HprovenanceFacts end.
match goal with Hfold : decodeItemByteFoldFacts args n 0 payloadStart lengthBytes |- _ => rename Hfold into HfoldFacts end.
unfold decodeItemEntryAt800d6a24.
iExists n, 0, payloadStart, lengthBytes, frameBytes, loaded.
cbn.
iSplit; first (iPureIntro; split; [zesu_pure_fact_hints_if_enabled|split; [unfold decodeItemDomainAt; split; [reflexivity|exact HdomainFacts]|split; assumption]]).
unfold decodeItemByteFoldStringHeader, decodeItemByteFoldResources, decodeItemBranchContinuation.
iFrame.
assert (Hcursor : (Z_to_bv 64 (decodeItemInputPointer args) + (Z_to_bv 64 n + 1))%bv = Z_to_bv 64 (payloadStart + n)) by zesu_pure_fact_hints_if_enabled.
assert (Hindex : (Z_to_bv 64 n + 1)%bv = Z_to_bv 64 (n + 1)) by bv_solve.
assert (Hstartbv : (Z_to_bv 64 (decodeItemInputPointer args) + 1)%bv = Z_to_bv 64 (payloadStart + 0)) by zesu_pure_fact_hints_if_enabled.
iEval (rewrite -Hcursor -Hindex -Hstartbv).
unfold decodeItemBranchContinuationAt.
cbn [Z.to_nat take bigEndian].
iFrame.
iEval (simpl; unfold reg_col).
iFrame.
iEval (rewrite /decodeItemSysRegs /zesu_sys_regs /machine_static_sys_regs /defaultMap /bigEndian /=).
iFrame.
assert (Hzero : Z_to_bv 64 0 = 0%bv) by bv_solve.
iEval (rewrite Hzero).
iFrame.
iSplit; first (iPureIntro; split; assumption).
done.
Unshelve.
all: prepare_sidecond.
all: try solve [reflexivity | bv_solve].
Qed.

Print Assumptions decodeItemInitialization6a14Native_correct.

