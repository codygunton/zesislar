Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArraySlices.
Require Import isla.isla.
Require Import ZesuSsz.Contracts.IslarisMemory.
Lemma byte_index_multiple :
  array_region_start 8 100
    (bv_unsigned ((BV 64 100) + bv_extract 0 64
      (bv_sign_extend 128 (BV 64 3) * bv_sign_extend 128 (BV 64 40)))) = 120%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma byte_index_overflow :
  ¬ (bv_unsigned (BV 64 (2 ^ 64 - 1)) + 1 * 40 < 2 ^ 64)%Z.
Proof. vm_compute. discriminate. Qed.
Lemma byte_index_bounds_rejected : ¬ (120 + 40 <= 159)%nat.
Proof. vm_compute. lia. Qed.
Print Assumptions byte_index_multiple.
