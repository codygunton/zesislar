Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import List ZArith NArith Lia.
Open Scope Z_scope.


Lemma s157_output16_index (base : Z) : Z.of_nat 16 = base + 16 - base.
Proof.
cbn. lia.
Qed.
Print Assumptions s157_output16_index.

Lemma s157_output24_index (base : Z) : Z.of_nat 24 = base + 24 - base.
Proof.
cbn. lia.
Qed.
Print Assumptions s157_output24_index.

Lemma s157_first_image_extent16 (storage prefix word : list byte) :
 List.length storage = 40%nat -> List.length prefix = 16%nat -> List.length word = 8%nat ->
 (16 + N.to_nat 8 <= List.length
   (prefix ++ drop 8 (drop 8 (take 32 storage ++ word ++ drop 40 storage))))%nat.
Proof.
intros Hstorage Hprefix Hword.
rewrite app_length !length_drop.
rewrite !app_length length_take length_drop.
rewrite Hstorage Hprefix Hword. cbn. lia.
Qed.
Print Assumptions s157_first_image_extent16.

Lemma s157_updated_image_extent24 (image word : list byte) (i j : nat) :
 List.length image = 40%nat -> List.length word = 8%nat -> i = 16%nat -> j = 24%nat ->
 (j + N.to_nat 8 <= List.length (take i image ++ word ++ drop (i + 8)%nat image))%nat.
Proof.
intros Himage Hword Hi Hj. subst i j.
rewrite !app_length !length_drop !length_take Himage Hword.
cbn. lia.
Qed.
Print Assumptions s157_updated_image_extent24.

Lemma s157_saved_frame_return_facts (args : DecodeItemArgs) (frame : list byte) :
 decodeItemSavedFrameFacts args frame ->
 (8 + N.to_nat 8 <= List.length frame)%nat /\ word64At frame 8 (decodeItemReturnAddress args).
Proof.
unfold decodeItemSavedFrameFacts. intros (Hlength & Hsaved & Hreturn).
split; [rewrite Hlength; cbn; lia | exact Hreturn].
Qed.
Print Assumptions s157_saved_frame_return_facts.
