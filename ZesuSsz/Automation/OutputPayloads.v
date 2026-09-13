Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

(* Normalize a known count and closed stack offsets in an output fragment. *)
Ltac zesu_normalize_output_payload :=
  try multimatch goal with
  | H : bv_unsigned ?word = Z.of_nat _
      |- context[bv_unsigned ?word] => rewrite H
  end;
  repeat progress multimatch goal with
  | |- context[bv_sub ?stack (bv_add ?left ?right)] =>
    let integer := eval vm_compute in (bv_unsigned (bv_add left right)) in
    lazymatch integer with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
    let Haddress := fresh "Haddress" in
    assert (Haddress : bv_sub stack (bv_add left right) =
      (stack - Z_to_bv 64 integer)%bv) by (clear; bv_solve);
    rewrite Haddress; clear Haddress
  end.
