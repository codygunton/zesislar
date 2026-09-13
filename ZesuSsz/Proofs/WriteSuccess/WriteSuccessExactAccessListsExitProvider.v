Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsLoopSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_exact_exit_provider `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) :
  □ (∀ (sp : bv 64) (base : Z) (entries : list writeSuccessAccessEntry)
     (bytes : list (bv 8)) (tail : spec) (savedX22 : bv 64),
   instr_body 0x153c0 (writeSuccessAccessListsLoopExit sp base entries bytes tail x19 savedX22 P)) -∗
  □ accessExactExitBodies x19 P.
Proof.
  iIntros "#Hexit". iModIntro. iIntros (sp base entries bytes tail savedX22).
  iPoseProof ("Hexit" $! sp base entries bytes tail savedX22) as "Hbody".
  iApply (instr_pre_wand 0x153c0 0x153c0 false false with "Hbody");
    [done | reflexivity |].
  iIntros "Hpost". iDestruct "Hpost" as (storedIndex x22 x27)
    "(Hsys & Hregs & Hsp & H19 & Hdata & Hcursor & H22 & H27 & Hbytes &
     Hown & Hscratch & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(_ & HP & _)".
  iExists storedIndex, x22, x27. iFrame.
Qed.
Print Assumptions access_exact_exit_provider.
