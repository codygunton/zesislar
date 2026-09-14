Require Import ZesuSsz.Automation.All.
Require Export ZesuSsz.Automation.ResourceGroups.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.

(* Resource algebra only. The final group retains every caller resource. *)
Lemma zesu_branch_resource_equiv {Sigma : gFunctors}
    (sys regs stack total cursor frame : iProp Sigma) :
  sys ∗ regs ∗ stack ∗ total ∗ cursor ∗ frame ⊣⊢
  sys ∗ total ∗ cursor ∗ (regs ∗ stack ∗ frame) ∗ True.
Proof.
  iSplit.
  - iIntros "(Hsys & Hregs & Hstack & Htotal & Hcursor & Hframe)". iFrame.
  - iIntros "(Hsys & Htotal & Hcursor & Hrest & _)".
    iDestruct "Hrest" as "(Hregs & Hstack & Hframe)". iFrame.
Qed.

(* A bits shape supplies a typed witness without changing its owner. *)
Ltac zesu_expose_bits_shape_values :=
  repeat match goal with
  | Hshape : valu_has_shape ?value (BitsShape 64) |- _ =>
      is_var value;
      let bits := fresh "registerBits" in
      let Hequal := fresh "registerBitsEqual" in
      destruct (valu_has_bits_shape value 64 Hshape) as [bits Hequal];
      subst value
  end.

(* Expose register values. Preserve fixed values and all shape facts. *)
Ltac zesu_open_bits_registers :=
  repeat first
    [ iSelect (reg_col ((KindReg _, BitsShape 64) :: _))%I
        ltac:(fun H =>
          iEval (rewrite reg_col_cons) in H;
          iDestruct H as "[? ?]";
          zesu_open_resource_groups)
    | let actual := fresh "registerValue" in
      iDestruct select (∃ value, ⌜valu_has_shape value (BitsShape 64)⌝ ∗
        _ ↦ᵣₖ value)%I as (actual) "?";
      zesu_open_resource_groups
    | let actual := fresh "registerValue" in
      iDestruct select (∃ value, ⌜valu_has_shape value (BitsShape 64)⌝ ∗
        _ ↦ᵣ value)%I as (actual) "?";
      zesu_open_resource_groups
    | let actual := fresh "registerValue" in
      iDestruct select (∃ value, ⌜value = _⌝ ∗ _ ↦ᵣ value)%I
        as (actual) "[%registerEquality ?]";
      subst actual; zesu_open_resource_groups
    | let actual := fresh "registerValue" in
      iDestruct select (∃ value, ⌜valu_has_shape value _⌝ ∗ _ ↦ᵣ value)%I
        as (actual) "?";
      zesu_open_resource_groups ];
  zesu_expose_bits_shape_values.

Ltac zesu_pack_register register :=
  let instantiate H :=
    let entry := iTypeOf H in
    lazymatch entry with
    | Some (_, ?r ↦ᵣ ?value)%I => zesu_pack (value, tt)ₗ
    | Some (_, KindReg ?r ↦ᵣₖ ?value)%I => zesu_pack (value, tt)ₗ
    end in
  first [iSelect (KindReg register ↦ᵣₖ _)%I instantiate
        |iSelect (register ↦ᵣ _)%I instantiate].

Ltac zesu_normalize_resource_addresses :=
  match goal with
  | Hlower : (?low <= bv_unsigned ?pointer)%Z,
    Hupper : (bv_unsigned ?pointer + _ < ?high)%Z
      |- context[bv_unsigned (bv_add ?pointer ?offset)] =>
      let ramLow := eval vm_compute in low in
      let ramHigh := eval vm_compute in high in
      let expectedLow := eval vm_compute in ((mapRamBase defaultMap)%Z) in
      let expectedHigh := eval vm_compute in ((machineRamEnd defaultMap)%Z) in
      constr_eq ramLow expectedLow; constr_eq ramHigh expectedHigh;
      let integer := eval vm_compute in (bv_unsigned offset) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      let Haddress := fresh "Haddress" in
      assert (Haddress : bv_unsigned (bv_add pointer offset) =
        (bv_unsigned pointer + integer)%Z) by
        (clear -Hlower Hupper; bv_solve);
      rewrite Haddress; clear Haddress
  end.
