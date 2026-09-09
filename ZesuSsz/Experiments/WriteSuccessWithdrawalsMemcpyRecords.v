From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.

Import ListNotations.

Lemma writeSuccessSegmentRecordsEmpty before observations :
  concat (map microLabels observations) = [] ->
  segmentRecords before observations = [].
Proof.
  intros Hlabels. unfold segmentRecords.
  revert Hlabels.
  generalize (seq_mem (snd before)).
  induction observations as [|observation rest IH]; intros memory Hlabels; cbn.
  - reflexivity.
  - apply app_eq_nil in Hlabels as (Hhead & Hrest).
    rewrite Hhead. cbn. apply IH. exact Hrest.
Qed.

Lemma writeSuccessConcatMicroLabelsApp first second :
  concat (map microLabels (first ++ second)) =
    concat (map microLabels first) ++ concat (map microLabels second).
Proof. rewrite map_app. rewrite concat_app. reflexivity. Qed.

Print Assumptions writeSuccessSegmentRecordsEmpty.
Print Assumptions writeSuccessConcatMicroLabelsApp.
