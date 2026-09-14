Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import isla.riscv64.riscv64.

Definition framedContractResources `{!islaG Sigma} `{!threadG}
    {Args Outcome : Type} (resources : IslarisContractResources Args Outcome)
    (P : iProp Sigma) : IslarisContractResources Args Outcome := {|
  islarisCode := islarisCode _ _ resources;
  islarisEntry := fun args => (islarisEntry _ _ resources args ∗ P)%I;
  islarisExit := fun args outcome => (islarisExit _ _ resources args outcome ∗ P)%I
|}.

Lemma IslarisContractSpec_frame `{!islaG Sigma} `{!threadG}
    {Args Outcome : Type} (entryPc exitPc : Z)
    (allows : Args -> Outcome -> Prop)
    (resources : IslarisContractResources Args Outcome) (P : iProp Sigma) :
  IslarisContractSpec entryPc exitPc allows resources -∗
  IslarisContractSpec entryPc exitPc allows (framedContractResources resources P).
Proof.
  rewrite /IslarisContractSpec /framedContractResources /=.
  iIntros "Hspec Hcode" (args).
  iPoseProof ("Hspec" with "Hcode") as "Hbody".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "[[Hentry HP] Hreturn]".
  iApply "Hbody".
  iFrame "Hentry".
  iNext.
  iIntros "Houtcome".
  iApply "Hreturn".
  iDestruct "Houtcome" as (outcome) "[Hallowed Hexit]".
  iExists outcome. iFrame.
Qed.
Print Assumptions IslarisContractSpec_frame.
