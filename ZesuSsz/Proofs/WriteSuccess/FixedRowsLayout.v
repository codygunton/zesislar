Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma fixed_rows_layout (width : nat) (prefix : list (list (bv 8))) row rest :
  Forall (fun bytes => length bytes = width) prefix -> length row = width ->
  length (concat prefix) = (width * length prefix)%nat /\
  take width (drop (width * length prefix) (concat (prefix ++ row :: rest))) = row.
Proof.
  intros Hprefix Hrow.
  have Hlength : length (concat prefix) = (width * length prefix)%nat.
  { induction Hprefix; cbn; [lia|]. rewrite app_length IHHprefix H. lia. }
  split; first exact Hlength.
  rewrite concat_app -Hlength drop_app_length /=.
  rewrite -Hrow take_app firstn_all Nat.sub_diag /= app_nil_r. reflexivity.
Qed.
Print Assumptions fixed_rows_layout.
