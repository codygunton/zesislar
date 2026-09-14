Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma array_cursor_base_index (row : bv 64) (base : Z) (index : nat) :
  bv_unsigned row = (base + Z.of_nat index)%Z ->
  Z.to_nat (bv_unsigned row - base) = index.
Proof.
  intros Hrow. rewrite Hrow.
  replace (base + Z.of_nat index - base)%Z with (Z.of_nat index) by lia.
  apply Nat2Z.id.
Qed.

Lemma array_cursor_index (row offset : bv 64) (base : Z)
    (bytes : list (bv 8)) (index count : nat) :
  bv_unsigned row = (base + Z.of_nat index)%Z ->
  bv_unsigned offset = Z.of_nat count ->
  ((mapRamBase defaultMap) <= base)%Z ->
  (base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z ->
  (index + count <= length bytes)%nat ->
  Z.to_nat (bv_unsigned (row + offset)%bv - base) = (index + count)%nat.
Proof.
  intros Hrow Hoffset Hmin Hmax Hbound.
  cbv [machineRamEnd defaultMap mapRamBase mapRamSize] in Hmin, Hmax.
  have Hsum : bv_unsigned (row + offset)%bv =
      (bv_unsigned row + Z.of_nat count)%Z by bv_solve.
  rewrite Hsum Hrow. apply Nat2Z.inj.
  rewrite Z2Nat.id; lia.
Qed.

Ltac zesu_normalize_array_cursor_base :=
  match goal with
  | Hcursor : bv_unsigned ?row = (?base + Z.of_nat ?index)%Z
      |- context[Z.to_nat (bv_unsigned ?row - ?base)] =>
      let Hindex := fresh "HarrayIndex" in
      pose proof (array_cursor_base_index row base index Hcursor) as Hindex;
      rewrite Hindex; clear Hindex
  end.

Ltac zesu_require_machine_ram_bounds minimum maximum :=
  let low := eval vm_compute in minimum in
  let high := eval vm_compute in maximum in
  let expectedLow := eval vm_compute in (mapRamBase defaultMap) in
  let expectedHigh := eval vm_compute in (machineRamEnd defaultMap) in
  constr_eq low expectedLow; constr_eq high expectedHigh.

Ltac zesu_normalize_array_cursor_offset :=
  match goal with
  | Hcursor : bv_unsigned ?row = (?base + Z.of_nat ?index)%Z,
    Hlower : (?minimum <= ?base)%Z,
    Hupper : (?base + Z.of_nat (length ?bytes) < ?maximum)%Z
      |- context[Z.to_nat (bv_unsigned (bv_add ?row ?offset) - ?base)] =>
      zesu_require_machine_ram_bounds minimum maximum;
      let integer := eval vm_compute in (bv_unsigned offset) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac end;
      let count := eval vm_compute in (Z.to_nat integer) in
      let Hindex := fresh "HarrayIndex" in
      assert (Hindex : Z.to_nat (bv_unsigned (bv_add row offset) - base) =
        (index + count)%nat) by
        (eapply array_cursor_index;
          [exact Hcursor | vm_compute; reflexivity | exact Hlower |
           exact Hupper | lia]);
      rewrite Hindex; clear Hindex
  end.

Ltac zesu_normalize_array_cursors :=
  repeat first [zesu_normalize_array_cursor_base |
    zesu_normalize_array_cursor_offset].
