Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsLoopSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_exact_exit_provider `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (entries : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (tail : spec) (x19 savedX22 : bv 64) (P : iProp Sigma) :
  □ instr_body 0x153c0 (writeSuccessAccessListsLoopExit sp base entries bytes tail x19 savedX22 P) -∗
  □ accessExactExitBodies sp base entries bytes tail x19 savedX22 P.
Proof. move => *. zesu_block. Qed.
Print Assumptions access_exact_exit_provider.
