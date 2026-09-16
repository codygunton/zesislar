Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.ArrayCopyComplete.
Require Import isla.riscv64.riscv64.
Lemma test_array_copy_complete (count : bv 64) (data wanted : list (bv 8)) :
  bv_unsigned count = Z.of_nat (length data) ->
  take (Z.to_nat (bv_unsigned count)) data = take (Z.to_nat (bv_unsigned count)) wanted ->
  data = take (Z.to_nat (bv_unsigned count)) wanted.
Proof. apply array_copy_complete. Qed.
Print Assumptions test_array_copy_complete.
