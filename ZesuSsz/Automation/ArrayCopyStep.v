Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayCursors.
Require Import ZesuSsz.Automation.ArrayCounterBounds.
Require Import ZesuSsz.Automation.ArrayCounterStep.
From Coq Require Import ZArith.ZArith.

Lemma array_copy_step (base : Z) start (source : list (bv 8))
    (src limit i : bv 64) (data : list (bv 8)) (byte : bv 8) :
  bv_unsigned src = (base + Z.of_nat start)%Z ->
  bv_unsigned limit = Z.of_nat (length data) ->
  (start + length data <= length source)%nat ->
  (bv_unsigned i <= bv_unsigned limit)%Z -> i <> limit ->
  ((mapRamBase defaultMap) <= base)%Z ->
  (base + Z.of_nat (length source) < (machineRamEnd defaultMap))%Z ->
  take (Z.to_nat (bv_unsigned i)) data = take (Z.to_nat (bv_unsigned i)) (drop start source) ->
  source !! Z.to_nat ((bv_unsigned (src + i)%bv - base) `div` 1) = Some byte ->
  take (Z.to_nat (bv_unsigned (i + BV 64 1)%bv))
    (<[Z.to_nat (bv_unsigned i `div` 1):=bv_extract 0 8 (bv_zero_extend 64 byte)]> data) =
  take (Z.to_nat (bv_unsigned (i + BV 64 1)%bv)) (drop start source).
Proof.
  intros Hcursor Hlength Hbound Hle Hne Hlow Hhigh Hprefix Hlookup.
  have Hoffset : bv_unsigned i = Z.of_nat (Z.to_nat (bv_unsigned i)).
  { rewrite Z2Nat.id; [reflexivity|clear -i; bv_solve]. }
  have Hreadbound : (start + Z.to_nat (bv_unsigned i) <= length source)%nat.
  { apply Nat2Z.inj_le. rewrite Nat2Z.inj_add Z2Nat.id; [|clear -i; bv_solve].
    apply Nat2Z.inj_le in Hbound. rewrite Nat2Z.inj_add in Hbound. lia. }
  have Hindex := array_cursor_index src i base source start (Z.to_nat (bv_unsigned i))
    Hcursor Hoffset Hlow Hhigh Hreadbound.
  rewrite Z.div_1_r Hindex in Hlookup.
  have Hwanted : drop start source !! Z.to_nat (bv_unsigned i) = Some byte by rewrite lookup_drop.
  have Hdata := array_counter_index_lt i limit data Hlength Hne Hle.
  rewrite Z.div_1_r in Hdata.
  rewrite (array_counter_next_nat i limit Hne Hle) Z.div_1_r.
  replace (bv_extract 0 8 (bv_zero_extend 64 byte)) with byte by (clear -byte; bv_solve).
  rewrite (take_S_r (<[Z.to_nat (bv_unsigned i):=byte]>data) _ byte).
  2: { rewrite list_lookup_insert; [reflexivity|exact Hdata]. }
  rewrite take_insert; [|lia]. rewrite Hprefix.
  rewrite (take_S_r (drop start source) _ byte Hwanted). reflexivity.
Qed.
Print Assumptions array_copy_step.
