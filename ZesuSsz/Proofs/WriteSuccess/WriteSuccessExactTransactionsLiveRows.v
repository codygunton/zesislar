Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma fixed_byte_rows_length width (rows : list (list (bv 8))) :
 Forall (fun row => length row = width) rows ->
 length (concat rows) = (width * length rows)%nat.
Proof.
 induction rows as [|row rows IH]; inversion 1; cbn; first lia.
 rewrite app_length H2 IH; [lia | assumption].
Qed.
Print Assumptions fixed_byte_rows_length.
