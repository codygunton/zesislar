Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma authorization_row_slice (prefix : list (list (bv 8))) row rest :
  Forall (fun bytes => length bytes = 144%nat) prefix ->
  length row = 144%nat ->
  take 144 (drop (144 * length prefix) (concat (prefix ++ row :: rest))) = row.
Proof.
  intros Hprefix Hrow.
  have Hlength : length (concat prefix) = (144 * length prefix)%nat.
  { induction Hprefix; cbn; [reflexivity|]. rewrite app_length IHHprefix H. lia. }
  rewrite concat_app -Hlength drop_app_length /=.
  rewrite -Hrow take_app firstn_all Nat.sub_diag /= app_nil_r. reflexivity.
Qed.
Print Assumptions authorization_row_slice.
