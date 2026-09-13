Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCounter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_control_exact_exit_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed remaining bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
  (writeSuccessExactAccessListsState sp base entries processed remaining bytes
    storedIndex x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P ∗
   ⌜Z_to_bv 64 (Z.of_nat (length processed)) = Z_to_bv 64 (Z.of_nat (length entries))⌝ ∗ True) -∗
  writeSuccessAccessListsLoopExit sp base entries bytes tail x19 savedX22 P.
Proof.
  iIntros "(Hstate & %Heq & _)".
  iDestruct "Hstate" as "(Hsys & Hregs & Hsp & H19 & Hdata & Hcursor & H22 & H27 &
    Hbytes & Hown & Hscratch & Hmmio & Htrace & %Hpartition & _ & _ & %Hcount &
    _ & _ & _ & _ & _ & HP & _)".
  have Hnil := access_counter_remaining_nil entries processed remaining Hpartition Hcount Heq.
  subst remaining.
  iEval (rewrite Heq) in "Hcursor".
  iEval (cbn [writeSuccessExactAccessListsEvents]) in "Htrace".
  iExists storedIndex, x22, x27. iFrame.
Qed.
Print Assumptions access_control_exact_exit_resources.
