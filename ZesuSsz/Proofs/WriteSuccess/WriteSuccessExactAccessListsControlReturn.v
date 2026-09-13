Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsControlEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsControl.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_control_return_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed remaining bytes storedIndex x19 savedX22 old_data data x22 x27 tail
    (P : iProp Sigma) :
  accessListsControlState sp (Z_to_bv 64 (Z.of_nat (length entries)))
    (Z_to_bv 64 (Z.of_nat (length processed))) data
    (accessControlFrame sp base entries processed remaining bytes
      storedIndex x19 savedX22 old_data x22 x27 tail P) -∗
  writeSuccessExactAccessListsState sp base entries processed remaining bytes
    storedIndex x19 savedX22 data x22 x27 tail P.
Proof.
  iIntros "(Hsys & Hsp & Hdata & Hcursor & Htotal & _ & _ & _ & Hframe & _)".
  iDestruct "Hframe" as "(Hregs & H19 & H22 & H27 & Hbytes & Hown & Hscratch &
    Hmmio & Htrace & Hpartition & Hencoding & Hlength & Hcount & Halign & Hlow & Hhigh &
    Hbaselow & Hbasehigh & HP & _)".
  iDestruct "Hscratch" as "(Hsaved & Hbase & Hindex & Hcopy & Hstack & Hkeys & _)".
  unfold writeSuccessExactAccessListsState, writeSuccessAccessListsScratch. iFrame.
Qed.
Print Assumptions access_control_return_resources.
