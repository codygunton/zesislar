Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayDynamicCursors.
Require Import isla.riscv64.riscv64.
Lemma test_dynamic_array_search `{!islaG Sigma} `{!threadG}
    (row offset limit : bv 64) base index count (bytes : list (bv 8)) :
  bv_unsigned row = (base + Z.of_nat index)%Z ->
  bv_unsigned limit = Z.of_nat count -> offset <> limit ->
  (bv_unsigned offset <= bv_unsigned limit)%Z ->
  (index + count <= length bytes)%nat ->
  ((mapRamBase defaultMap) <= base)%Z ->
  (base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z ->
  base ↦ₘ∗ bytes -∗ find_in_context
    (FindMemMapsTo (bv_unsigned (row + offset)%bv)) (fun _ => True)%I.
Proof. intros Hrow Hlimit Hne Hle Hbound Hlow Hhigh. iStartProof. iIntros "Harray". liARun. Qed.
Print Assumptions test_dynamic_array_search.
