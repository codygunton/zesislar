Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.InstructionLookup.
Require Import ZesuSsz.Automation.Switches.StackWrite.
Require Import ZesuSsz.Automation.Switches.RamFault.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import Lia.
From iris.proofmode Require Import environments.

Ltac decode_item_prologue_at_branch _ :=
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindInstrKind 0x800d6970 _) _) => idtac
  end.

Lemma decodeItemPrologueTo6974Bridge_correct : decodeItemPrologueTo6974Bridge.
Proof.
  unfold decodeItemPrologueTo6974Bridge.
  intros Sigma HG HT returnAddress args Hnonzero.
  iIntros "Hcode".
  iEval (unfold decodeItemSelectedCode) in "Hcode".
  iDestruct "Hcode" as "#Hcode".
  iStartProof.
  repeat first [progress iIntros (?) | progress iIntros "#?" |
    progress iIntros "?"].
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run_until decode_item_prologue_at_branch.
  zesu_expose_environment_alias.
  iRename select ((decodeItemStackPointer args + -16 + 0) ↦ₘ decodeItemSavedFramePointer args)%I into "Hlow".
  iRename select ((decodeItemStackPointer args + -16 + 8) ↦ₘ Z_to_bv 64 (decodeItemReturnAddress args))%I into "Hhigh".
  iEval (replace (decodeItemStackPointer args + -16 + 8)%Z with
    (decodeItemStackPointer args + -16 + 0 + 8)%Z by lia) in "Hhigh".
  iDestruct (mem_mapsto_u64_pair_to_byte_array with "Hlow Hhigh") as "Hframe".
  iRename select ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes) ↦ₘ? (decodeItemStackPointer args + -16 + 0 - (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)))%I into "Hempty".
  iEval (replace (decodeItemStackPointer args + -16 + 0 -
    (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))%Z
    with 0%Z by (unfold RlpDecodeItem.decodeItemStackBytes; lia)) in "Hempty".
  iEval (rewrite mem_mapsto_uninit_0) in "Hempty".
  iDestruct "Hempty" as %HframeRange.
  zesu_run.
  all: try solve [exfalso; apply Hnonzero; rewrite H11; reflexivity].
  1: (unfold RlpDecodeItem.decodeItemStackBytes; bv_solve).
  destruct H as [Hra Hdom]. subst returnAddress.
  iExists (bv_to_little_endian 8 8 (bv_unsigned (decodeItemSavedFramePointer args)) ++ bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemReturnAddress args))), tt)ₗ.
  iEval (replace (decodeItemStackPointer args + -16 + 0)%Z with
    (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)%Z
    by (unfold RlpDecodeItem.decodeItemStackBytes; lia)) in "Hframe".
  iFrame "Hframe".
  iSplit; last done.
  iSplit.
  { iPureIntro. split.
    - apply decodeItemSavedFrameFacts_machine_words. exact Hdom.
    - unfold decodeItemDomainAt. split; [reflexivity | exact Hdom]. }
  iEval (unfold decodeItemBranchContinuation).
  iEval (unfold decodeItemBranchContinuationAt).
  iFrame.
Unshelve.
all: prepare_sidecond.
all: try reflexivity.
all: try (unfold RlpDecodeItem.decodeItemStackBytes; lia).
all: try bv_solve.
Qed.

Print Assumptions decodeItemPrologueTo6974Bridge_correct.
