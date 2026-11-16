From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Open Scope Z_scope.

(* A stack address `sp - 400 + 400 - 88`, wrapped at 2^64, with the range
   facts a block states on its signed 128-bit zero extension. The goal states
   the address against its unwrapped form. lia on these facts does not
   prove it; the stack-range step does. *)
Lemma stack_range_unwrapped_difference (sp : bv 64)
    (Hlow : bv_signed (bv_zero_extend 128
      (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551528)%bv)
      >= bv_signed (BV 128 2684354560))
    (Hhigh : bv_signed (bv_zero_extend 128
      (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551528)%bv
      + BV 128 2)%bv <= bv_signed (BV 128 3221225472)) :
  0 <= bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551528)%bv
    - (bv_unsigned sp - 400 + 48 + 56 + 176).
Proof.
  Fail solve [Lia.lia].
  ZesuSsz.Automation2.StackRange.zesu_stack_range_lia.
Qed.
Print Assumptions stack_range_unwrapped_difference.

(* The same address as a window offset inside a local definition: the offset
   becomes its constant. *)
Lemma stack_range_window_offset (sp : bv 64) (bytes : list (bv 8))
    (Hlow : bv_signed (bv_zero_extend 128
      (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551528)%bv)
      >= bv_signed (BV 128 2684354560))
    (Hhigh : bv_signed (bv_zero_extend 128
      (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551528)%bv
      + BV 128 2)%bv <= bv_signed (BV 128 3221225472)) :
  let window := skipn (Z.to_nat
    (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551528)%bv
     - (bv_unsigned sp - 400 + 48 + 56 + 176))) bytes in
  window = skipn 32 bytes.
Proof.
  intros window.
  Fail reflexivity.
  ZesuSsz.Automation2.StackRange.zesu_stack_offsets.
  reflexivity.
Qed.
Print Assumptions stack_range_window_offset.
