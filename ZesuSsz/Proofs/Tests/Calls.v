Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.

Lemma test_zesu_call `{!islaG Sigma} `{!threadG}
    (stack_size : Z)
    (P : list (bv 64) -> bv 64 ->
      ((list (bv 64) -> iProp Sigma) -> iProp Sigma) -> iProp Sigma) :
  zesu_call stack_size P -∗ zesu_call stack_size P.
Proof.
  iStartProof. iIntros "Hcall". iExact "Hcall".
Qed.

Print Assumptions test_zesu_call.
