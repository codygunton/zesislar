Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.ReadInput.ReadInput.
Definition mainReadInputFramedResources `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
    IslarisContractResources ReadInputArgs ReadInputOutcome := {|
  islarisCode := islarisCode _ _ read_input_resources;
  islarisEntry := fun args => (islarisEntry _ _ read_input_resources args ∗ P ∗ True)%I;
  islarisExit := fun args outcome => (islarisExit _ _ read_input_resources args outcome ∗ P ∗ True)%I
|}.
Lemma main_read_input_framed_state_correct `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  ⊢ IslarisContractSpec 0x10140 0x14ccc readInputAllows (mainReadInputFramedResources P).
Proof.
  rewrite /IslarisContractSpec /mainReadInputFramedResources /=.
  iIntros "Hcode" (args).
  iPoseProof (read_input_state_correct with "Hcode") as "Hread".
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hread".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "[(Hentry&HP&_) Hreturn]".
  iApply ("Hread" $! args). iFrame "Hentry".
  iNext. iIntros "Hexit". iDestruct "Hexit" as (outcome) "[Hallowed Hexit]".
  iApply "Hreturn". iExists outcome. iFrame.
Qed.
Print Assumptions main_read_input_framed_state_correct.
