Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ArrayCursors.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma array_byte_lookup (bytes : list (bv 8)) (index : nat) (byte : bv 8) :
  bytes !! index = Some byte ->
  bv_zero_extend 64 byte =
    Z_to_bv 64 (little_endian_to_bv 8 (take 1 (drop index bytes))).
Proof.
  intros Hlookup.
  have Hhead : drop index bytes !! 0%nat = Some byte.
  { rewrite lookup_drop Nat.add_0_r. exact Hlookup. }
  destruct (drop index bytes) as [|head rest] eqn:Hdrop; simpl in Hhead;
    inversion Hhead; subst.
  cbn. bv_solve.
Qed.

Ltac zesu_normalize_array_byte_lookups :=
  repeat match goal with
  | Hlookup : ?bytes !! Z.to_nat
      ((bv_unsigned (bv_add ?row ?offset) - ?base) `div` 1) = Some ?byte,
    Hcursor : bv_unsigned ?row = (?base + Z.of_nat ?index)%Z,
    Hlower : (0x20000000 <= ?base)%Z,
    Hupper : (?base + Z.of_nat (length ?bytes) < 0x40000000)%Z |- _ =>
      let integer := eval vm_compute in (bv_unsigned offset) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac end;
      let count := eval vm_compute in (Z.to_nat integer) in
      let Hindex := fresh "HarrayByteIndex" in
      assert (Hindex : Z.to_nat (bv_unsigned (bv_add row offset) - base) =
        (index + count)%nat) by
        (eapply array_cursor_index;
          [exact Hcursor | vm_compute; reflexivity | exact Hlower |
           exact Hupper | lia]);
      rewrite Z.div_1_r Hindex in Hlookup; clear Hindex
  end.

Ltac zesu_array_byte_value :=
  zesu_normalize_array_byte_lookups;
  eapply array_byte_lookup; eassumption.
