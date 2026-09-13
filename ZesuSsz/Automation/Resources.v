Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

(* Open separating groups. Keep memory arrays and register collections whole. *)
Ltac zesu_open_resource_groups :=
  repeat first
    [ iDestruct select (_ ∗ _)%I as "[? ?]"
    | iDestruct select (⌜_⌝)%I as %? ].

Ltac zesu_normalize_resource_addresses :=
  match goal with
  | Hlower : (?low <= bv_unsigned ?pointer)%Z,
    Hupper : (bv_unsigned ?pointer + _ < ?high)%Z
      |- context[bv_unsigned (bv_add ?pointer ?offset)] =>
      let ramLow := eval vm_compute in low in
      let ramHigh := eval vm_compute in high in
      let expectedLow := eval vm_compute in (0x20000000%Z) in
      let expectedHigh := eval vm_compute in (0x40000000%Z) in
      constr_eq ramLow expectedLow; constr_eq ramHigh expectedHigh;
      let integer := eval vm_compute in (bv_unsigned offset) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      let Haddress := fresh "Haddress" in
      assert (Haddress : bv_unsigned (bv_add pointer offset) =
        (bv_unsigned pointer + integer)%Z) by
        (clear -Hlower Hupper; bv_solve);
      rewrite Haddress; clear Haddress
  end.
