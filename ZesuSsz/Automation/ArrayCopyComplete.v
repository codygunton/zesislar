Require Import isla.riscv64.riscv64.
Lemma array_copy_complete {A} (count : bv 64) (data wanted : list A) :
  bv_unsigned count = Z.of_nat (length data) ->
  take (Z.to_nat (bv_unsigned count)) data = take (Z.to_nat (bv_unsigned count)) wanted ->
  data = take (Z.to_nat (bv_unsigned count)) wanted.
Proof.
  intros Hsize Hprefix.
  have Hcount : Z.to_nat (bv_unsigned count) = length data by rewrite Hsize Nat2Z.id.
  rewrite Hcount in Hprefix |- *.
  rewrite (take_ge data) in Hprefix; [exact Hprefix|lia].
Qed.
Print Assumptions array_copy_complete.
