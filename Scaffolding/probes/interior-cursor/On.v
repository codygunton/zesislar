Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.IntegerArrayAddress.
Lemma fold_cursor `{!islaG Sigma} `{!threadG}
    (base payloadStart i n : Z) (bytes : list (bv 8))
    (Hbounds : 0 <= base /\ base + Z.of_nat (length bytes) < 2 ^ 64)
    (Hfold : payloadStart = base + 1 /\ 0 <= i < n /\
      payloadStart + n <= base + Z.of_nat (length bytes)) :
  let LET0 := (Z_to_bv 64 (payloadStart + i) + 0)%bv in
  base ↦ₘ∗ bytes -∗
  find_in_context (FindMemMapsTo (bv_unsigned LET0)) (fun _ => True)%I.
Proof.
  intros LET0. iStartProof. iIntros "Hbytes".
  zesu_integer_array_address_if_enabled.
  zesu_run.
Qed.
Print Assumptions fold_cursor.
