Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ByteLists.

Lemma byte_list_end_advance (pointer : bv 64)
    (item : ByteListItem) (rest : list ByteListItem) :
  byteListEndPointer pointer (item :: rest) =
  byteListEndPointer (pointer + BV 64 16)%bv rest.
Proof. unfold byteListEndPointer. bv_solve. Qed.
Print Assumptions byte_list_end_advance.
#[export] Hint Rewrite byte_list_end_advance : zesu_indices.
#[export] Hint Rewrite <- app_assoc : zesu_indices.
#[export] Hint Rewrite app_nil_r : zesu_indices.

Ltac zesu_open_processed_resources :=
  repeat iSelect (byteListProcessedResources _ _)%I
    ltac:(fun H => iEval (unfold byteListProcessedResources) in H).

Lemma simplify_goal_byte_list_processed_nil `{!islaG Sigma}
    (address : Z) (T : iProp Sigma) :
  T ⊢ simplify_goal (byteListProcessedResources address []) T.
Proof.
  unfold simplify_goal. iIntros "HT". iFrame "HT".
  iApply byteListProcessedResources_nil.
Qed.
Print Assumptions simplify_goal_byte_list_processed_nil.
Definition simplify_goal_byte_list_processed_nil_inst :=
  [instance @simplify_goal_byte_list_processed_nil with 0%N].
Global Existing Instance simplify_goal_byte_list_processed_nil_inst.

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
