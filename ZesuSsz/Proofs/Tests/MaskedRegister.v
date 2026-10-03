Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Lemma mask_dispatch_positive (value : bv 64) :
  Z.land (bv_unsigned value) 131072 = 0 →
  Val_Bool (bool_decide (bv_and value (BV 64 131072) = BV 64 0)) = Val_Bool true.
Proof. intro Hmask. zesu_finish_mask. Qed.
Lemma mask_dispatch_missing (value : bv 64) :
  Val_Bool (bool_decide (bv_and value (BV 64 131072) = BV 64 0)) =
  Val_Bool true ∨ True.
Proof. Fail solve [left; zesu_finish_mask]. right. exact I. Qed.
Lemma mask_dispatch_wrong :
  Val_Bool (bool_decide (bv_and (BV 64 131072) (BV 64 131072) = BV 64 0)) ≠ Val_Bool true.
Proof. vm_compute. discriminate. Qed.
Print Assumptions mask_dispatch_positive.
