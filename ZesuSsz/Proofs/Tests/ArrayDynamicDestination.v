Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayDynamicDestination.
Require Import isla.riscv64.riscv64.
Lemma test_dynamic_destination_search `{!islaG Sigma} `{!threadG}
    (row offset limit : bv 64) (bytes : list (bv 8)) :
  bv_unsigned limit = Z.of_nat (length bytes) -> offset <> limit ->
  (bv_unsigned offset <= bv_unsigned limit)%Z ->
  ((mapRamBase defaultMap) <= bv_unsigned row)%Z ->
  (bv_unsigned row + bv_unsigned limit < (machineRamEnd defaultMap))%Z ->
  bv_unsigned row ↦ₘ∗ bytes -∗ find_in_context
    (FindMemMapsTo (bv_unsigned (row + offset)%bv)) (fun _ => True)%I.
Proof. intros Hlimit Hne Hle Hlow Hhigh. iStartProof. iIntros "Harray". liARun. Qed.
Print Assumptions test_dynamic_destination_search.
