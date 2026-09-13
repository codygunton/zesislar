Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.

Lemma simplify_goal_byte_list_processed_snoc `{!islaG Sigma}
    (address : Z) (done : list ByteListItem) (item : ByteListItem)
    (T : iProp Sigma) :
  (byteListProcessedResources address done ∗
   byteListItemResources (address + 16 * Z.of_nat (length done)) [item] ∗ T) ⊢
  simplify_goal (byteListProcessedResources address (done ++ [item])) T.
Proof.
  unfold simplify_goal. iIntros "(Hdone & Hitem & HT)". iFrame "HT".
  iApply (byteListProcessedResources_snoc with "Hdone Hitem").
Qed.
Print Assumptions simplify_goal_byte_list_processed_snoc.
Definition simplify_goal_byte_list_processed_snoc_inst :=
  [instance @simplify_goal_byte_list_processed_snoc with 0%N].
Global Existing Instance simplify_goal_byte_list_processed_snoc_inst.

Lemma simplify_goal_byte_list_processed_last `{!islaG Sigma}
    (address : Z) (done : list ByteListItem) (item : ByteListItem)
    (T : iProp Sigma) :
  (byteListProcessedResources address done ∗
   byteListItemResources (address + 16 * Z.of_nat (length done)) [item] ∗ T) ⊢
  simplify_goal (byteListItemResources address (done ++ [item])) T.
Proof.
  unfold simplify_goal. iIntros "(Hdone & Hitem & HT)". iFrame "HT".
  iApply (byteListProcessedResources_combine with "Hdone Hitem").
Qed.
Print Assumptions simplify_goal_byte_list_processed_last.
Definition simplify_goal_byte_list_processed_last_inst :=
  [instance @simplify_goal_byte_list_processed_last with 0%N].
Global Existing Instance simplify_goal_byte_list_processed_last_inst.
