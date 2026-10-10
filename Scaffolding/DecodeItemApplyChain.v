Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Compliance.DecodeItemC1BMeaning.
Require Import Scaffolding.DecodeItemComplianceStatement.
Require Import Scaffolding.DecodeItemSignatureGates.

Definition decodeItemComposedC1BModel (returnAddress : Z) :
    IslarisContractModel DecodeItemArgs DecodeItemOutcome :=
  let selected := decodeItemSelectedModel returnAddress in
  {| islarisContractAllows := fun args after =>
       decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
       decodeItemAllowsC1B args after;
     islarisContractStep := islarisContractStep _ _ selected;
     islarisContractResources := islarisContractResources _ _ selected |}.

Lemma decodeItemC1BExitBridge `{!islaG Sigma} `{!threadG}
    returnAddress args :
  (∃ after, ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
       decodeItemAllowsC1B args after⌝ ∗ decodeItemExitResources args after) ⊢
  (∃ after, ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
       DecodeMeaningModuloKnownBugs args after⌝ ∗ decodeItemExitResources args after).
Proof.
  iIntros "Hafter". iDestruct "Hafter" as (after) "[%Hallows Hexit]".
  iExists after. iFrame. iPureIntro.
  destruct Hallows as [Hdomain Hallows]. split; first exact Hdomain.
  apply decodeItemC1BMeaning; first exact (proj2 Hdomain). exact Hallows.
Qed.

Lemma decodeItemC1BSelectedCompliance :
  (forall returnAddress, IslarisContractCorrect decodeItemEntry returnAddress
    (decodeItemComposedC1BModel returnAddress)) ->
  DecodeItemComplianceStatement.
Proof.
  intros Hcomposed returnAddress Sigma HG HT.
  pose proof (Hcomposed returnAddress Sigma HG HT) as HcomposedSpec.
  unfold IslarisContractSpec in HcomposedSpec.
  unfold IslarisContractSpec.
  iIntros "Hcode". iIntros (args).
  iPoseProof (HcomposedSpec with "Hcode") as "Hbody".
  iSpecialize ("Hbody" $! args).
  iApply (instr_pre_wand with "Hbody []"); [done|done|].
  iIntros "[Hentry Hreturn]". iFrame "Hentry".
  iApply (instr_pre_wand with "Hreturn []"); [done|done|].
  iIntros "Hafter". iApply (decodeItemC1BExitBridge with "Hafter").
Qed.

Print Assumptions decodeItemC1BExitBridge.
Print Assumptions decodeItemC1BSelectedCompliance.
