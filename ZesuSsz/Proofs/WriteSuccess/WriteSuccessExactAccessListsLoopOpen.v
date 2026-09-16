Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsLoopSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_loop_open_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed remaining bytes storedIndex x19 savedX22 data pointer count tail
    (P : iProp Sigma) :
  instr_pre 0x153c0 (writeSuccessAccessListsLoopExit sp base entries bytes tail x19 savedX22 P) -∗
  writeSuccessExactAccessListsState sp base entries processed remaining bytes storedIndex
    x19 savedX22 data pointer count tail P -∗
  writeSuccessExactAccessListsState sp base entries processed remaining bytes storedIndex
    x19 savedX22 data pointer count tail
    (accessExactLoopFrame sp base entries bytes tail x19 savedX22 P).
Proof.
  iIntros "Hnext Hstate". iDestruct "Hstate" as
    "(Hsys & Hregs & Hsp & H19 & Hdata & Hcursor & Hptr & Hcount & Hbytes & Hown &
     Hscratch & Hmmio & Htrace & Hpartition & Hencoding & Hlength & Htotalbound & Halign &
     Hlow & Hhigh & Hbaselow & Hbasehigh & HP & _)".
  unfold writeSuccessExactAccessListsState, accessExactLoopFrame. iFrame.
Qed.
Print Assumptions access_loop_open_resources.
