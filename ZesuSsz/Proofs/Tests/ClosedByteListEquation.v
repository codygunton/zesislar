From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* decodeParentHeader 05a4/04b0/0570: the successor asks the byte stored after
   a word as `[1]`, the block holds the byte cell as `bv_extract 0 8 1` (the
   low byte of the stored register value). The list equation of two closed
   lists is decided by computation in Finish.zesu_finish_known_list_shape;
   `reflexivity` refuses it (the well-formedness proofs differ as terms). *)
Lemma test_closed_byte_list_equation :
  [BV 8 1] = [bv_extract 0 8 (BV 64 1)].
Proof. ZesuSsz.Automation2.Finish.zesu_finish_known_list_shape. Qed.

(* A list with a variable is not closed: the computation is not tried, and
   no other alternative proves the (unprovable) equation. *)
Lemma test_closed_byte_list_equation_open (b : bv 8) : True.
Proof.
  Fail assert ([b] = [bv_extract 0 8 (BV 64 1)])
    by ZesuSsz.Automation2.Finish.zesu_finish_known_list_shape.
  exact I.
Qed.

Print Assumptions test_closed_byte_list_equation.
