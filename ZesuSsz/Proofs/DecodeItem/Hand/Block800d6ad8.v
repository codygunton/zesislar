Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import SailStdpp.MachineWord.
From iris.proofmode Require Import environments.

Definition DesignedEntry_800d6ad8
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ad8 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6ad8) := I.
Global Typeclasses Opaque DesignedEntry_800d6ad8.


Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Lemma DesignedBoundary_800d6ad8 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte)   :
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  instr_pre 0x800d6b08 (∃ (successor_locals : DecodeItemReturnLocals) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_headerLength : Z) (successor_payloadLength : Z), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6b08 (args) (successor_locals) (successor_inputPrefix) (successor_rest) (successor_headerLength) (successor_payloadLength))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6ad8
    (DesignedEntry_800d6ad8 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest).
Proof.
  iStartProof.
  zesu_expose_code_lists.
  repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
  zesu_reduce_introduced_code_lists.
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  let switches := zesu_search_switches in zesu_dispatch_search switches ltac:(fun _ => zesu_liAStep).
  zesu_expose_environment_alias; let switches := zesu_search_switches in zesu_dispatch_search switches ltac:(fun _ => zesu_liAStep).
  zesu_expose_environment_alias; let switches := zesu_search_switches in zesu_dispatch_search switches ltac:(fun _ => zesu_expose_instruction_lookup).
  zesu_expose_environment_alias; let switches := zesu_search_switches in zesu_dispatch_search switches ltac:(fun _ => zesu_liAStep).
  iSplitR; [iPureIntro; vm_compute; eauto|].
  iIntros "Hentry HPC".
  iEval (unfold DesignedEntry_800d6ad8, decodeItemEntryAt800d6ad8) in "Hentry".
  iDestruct "Hentry" as "[Hentry _]".
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_expose_environment_alias; unfold a800d6ad8.
  zesu_expose_environment_alias; let switches := zesu_search_switches in zesu_dispatch_search switches ltac:(fun _ => zesu_liAStep).
  repeat (zesu_expose_environment_alias; liShow; lazymatch goal with | |- envs_entails _ (find_in_context (FindInstrKind 0x800d6ae0 _) _) => fail 0 | |- envs_entails _ (find_in_context (FindInstrKind 0x800d6b08 _) _) => fail 0 | _ => let switches := zesu_search_switches in zesu_dispatch_search switches ltac:(fun _ => zesu_liAStep) end); liShow.
  iMatchHyp ltac:(fun Hresource body => lazymatch body with | decodeItemByteFoldResources _ _ _ _ _ _ _ _ => iEval (unfold decodeItemByteFoldResources) in Hresource end).
  zesu_open_resource_groups.
  zesu_expose_environment_alias; let switches := zesu_search_switches in zesu_dispatch_search switches ltac:(fun _ => zesu_liAStep).
  repeat (zesu_expose_environment_alias; liShow; lazymatch goal with | |- envs_entails _ (find_in_context (FindInstrKind 0x800d6ae0 _) _) => fail 0 | |- envs_entails _ (find_in_context (FindInstrKind 0x800d6b08 _) _) => fail 0 | _ => let switches := zesu_search_switches in zesu_dispatch_search switches ltac:(fun _ => zesu_liAStep) end); liShow.
  2: (match goal with Hfault : ?bit = 1%bv |- _ => zesu_stack_closed_term bit; assert (HnoFault : bit <> 1%bv) by (vm_compute; discriminate); exfalso; exact (HnoFault Hfault) end).
  1: (zesu_expose_environment_alias; let switches := zesu_search_switches in zesu_dispatch_search switches ltac:(fun _ => zesu_liAStep)).
  all: destruct H2 as (Hdomain & Hprovenance & HsavedFrame).
  1: (destruct Hprovenance as (HinputHead & HprefixClass & Hwidth & Hstart & HlengthBytes); subst n payloadStart; iExists (decodeItemCompletedFoldLocals args (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1) lengthBytes frameBytes loaded), inputPrefix, rest, (1 + (bv_unsigned inputPrefix - 247)), (RlpDecodeItem.bigEndian lengthBytes)).
  1: assert (Htake : take (Z.to_nat (bv_unsigned inputPrefix - 247)) lengthBytes = lengthBytes) by (rewrite HlengthBytes take_take Nat.min_id; reflexivity).
  1: (zesu_expose_environment_alias; unfold decodeItemEntryAt800d6b08, decodeItemReturnEntryCore; cbn [decodeItemCompletedFoldLocals]).
  1: cbn [decodeItemCompletedFoldLocals returnA1 returnA2 returnA3 returnA4 returnA5 returnA6 returnStorage returnFrame].
  1: rewrite Htake.
  1: pose proof (decodeItemCompletedFoldConsumedWord args (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1) lengthBytes (proj2 H1)) as Hconsumed.
  1: rewrite Htake in Hconsumed.
  1: (unfold LET0; rewrite Hconsumed; iFrame).
  1: (rewrite Htake; iFrame).
  1: pose proof (proj2 H1) as Hfold.
  1: assert (Hfits : decodeItemFoldLengthFits args (bv_unsigned inputPrefix - 247) lengthBytes = true).
  1: apply (decodeItemCompletedFoldFitsGuard args (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1) lengthBytes Hfold).
  1: unfold LET0 in H5.
  1: (apply Z.le_ngt; apply Z.ge_le; exact H5).
  1: assert (Hprovenance : decodeItemFoldProvenance args true inputPrefix rest (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1) lengthBytes) by repeat first [assumption | reflexivity | split].
  1: pose proof (decodeItemCompletedFoldAcceptedWitnessFacts args true inputPrefix rest (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1) lengthBytes Hdomain Hprovenance Hfold Hfits) as Haccepted.
  1: pose proof (decodeItemCompletedFoldWordValues args (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1) lengthBytes Hdomain Hfold) as (Hcursor & Hpayload & HconsumedValue).
  1: pose proof (decodeItemCompletedFoldValueBounds args (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1) lengthBytes Hfold) as Hvalue.
  1: rewrite <- Hconsumed.
  1: iSplit.
  1: iPureIntro.
  1: (unfold decodeItemDomainAt; pose proof Hdomain as HdomainFacts; destruct HdomainFacts as (_ & HstorageLength & _); repeat first [assumption | reflexivity | split]).
  1: (iPureIntro; repeat first [assumption | reflexivity | split | congruence]).
  1: (rewrite HlengthBytes; reflexivity).
  1: exact (proj1 Hvalue).
  1: (zesu_expose_environment_alias; let switches := zesu_search_switches in zesu_dispatch_search switches ltac:(fun _ => zesu_liAStep)).
  destruct Hprovenance as (HinputHead & HprefixClass & Hwidth & Hstart & HlengthBytes); subst n payloadStart; iExists (decodeItemCompletedFoldLocals args (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1) lengthBytes frameBytes loaded).
  assert (Htake : take (Z.to_nat (bv_unsigned inputPrefix - 247)) lengthBytes = lengthBytes) by (rewrite HlengthBytes take_take Nat.min_id; reflexivity).
  zesu_expose_environment_alias; unfold decodeItemEntryAt800d6ae0, decodeItemReturnEntryCore; cbn [decodeItemCompletedFoldLocals returnA1 returnA2 returnA3 returnA4 returnA5 returnA6 returnStorage returnFrame].
  pose proof (proj2 H1) as Hfold.
  pose proof (decodeItemCompletedFoldConsumedWord args (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1) lengthBytes Hfold) as Hconsumed.
  rewrite Htake in Hconsumed.
  unfold LET0; rewrite Htake Hconsumed; iFrame.
  assert (Hprovenance : decodeItemFoldProvenance args true inputPrefix rest (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1) lengthBytes) by repeat first [assumption | reflexivity | split].
  assert (Hreject : decodeItemFoldLengthFits args (bv_unsigned inputPrefix - 247) lengthBytes = false) by (apply (decodeItemCompletedFoldRejectGuard args (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1) lengthBytes Hfold); unfold LET0 in H5; apply Z.nle_gt; intro Hle; apply H5; apply Z.le_ge; exact Hle).
  pose proof (decodeItemCompletedFoldRejected args true inputPrefix rest (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1) lengthBytes Hdomain Hprovenance Hfold Hreject) as Hrejected.
  iSplit.
  1: (iPureIntro; unfold decodeItemDomainAt; pose proof Hdomain as HdomainFacts; destruct HdomainFacts as (_ & HstorageLength & _); repeat first [assumption | reflexivity | split]).
  iPureIntro; split; [exact Hrejected | reflexivity].
  Unshelve.
  all: prepare_sidecond.
  all: (apply bv_eq; reflexivity).
Qed.
