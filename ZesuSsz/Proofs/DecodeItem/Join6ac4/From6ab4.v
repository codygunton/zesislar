Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.InstructionLookup.
Require Import ZesuSsz.Automation.Switches.RamFault.
Require Import ZesuSsz.Automation.Switches.EvarSideconditionGuard.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldInitializationWitnesses.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Open Scope Z_scope.

Lemma decodeItemJoin6ac4From6ab4_correct `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte) (oldAcc oldCursor loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  ⊢ decodeItemJoin6ac4From6ab4 args n payloadStart lengthBytes frameBytes
      oldAcc oldCursor loaded inputPrefix rest.
Proof.
unfold decodeItemJoin6ac4From6ab4, decodeItemJoinTransferObligation.
iIntros "Hcode".
iEval (unfold decodeItemSelectedCode) in "Hcode".
iDestruct "Hcode" as "#Hcode".
Timeout 300 zesu_block.
match goal with Hdomain : decodeItemC1BDomain args |- _ => rename Hdomain into HdomainFacts end.
match goal with Hprovenance : decodeItemFoldProvenance args true inputPrefix rest n payloadStart lengthBytes |- _ => rename Hprovenance into HprovenanceFacts end.
match goal with Hfold : decodeItemByteFoldFacts args n 0 payloadStart lengthBytes |- _ => rename Hfold into HfoldFacts end.
iExists (loaded, frameBytes, lengthBytes, payloadStart, 0, n, tt)ₗ.
cbn.
iSplit; first (iPureIntro; exact (decodeItemByteFoldFirstGuard args n payloadStart lengthBytes HfoldFacts)).
iSplit; first (iPureIntro; split; [unfold decodeItemDomainAt; split; [reflexivity|exact HdomainFacts]|split; assumption]).
unfold decodeItemByteFoldListHeader, decodeItemByteFoldResources, decodeItemBranchContinuation.
iFrame.
assert (Hstart : payloadStart = decodeItemInputPointer args + 1) by (unfold decodeItemFoldProvenance in HprovenanceFacts; tauto).
assert (Hcursor : (Z_to_bv 64 (decodeItemInputPointer args) + (Z_to_bv 64 n + 1))%bv = Z_to_bv 64 (payloadStart + n)) by (rewrite Hstart; bv_solve).
assert (Hindex : (Z_to_bv 64 n + 1)%bv = Z_to_bv 64 (n + 1)) by bv_solve.
assert (Hstartbv : (Z_to_bv 64 (decodeItemInputPointer args) + 1)%bv = Z_to_bv 64 (payloadStart + 0)) by (rewrite Hstart; bv_solve).
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

Print Assumptions decodeItemJoin6ac4From6ab4_correct.

