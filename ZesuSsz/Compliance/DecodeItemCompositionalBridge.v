Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Compliance.DecodeItemCompositionalWeakening.

Lemma decodeItemRegisterComplianceWeakens returnAddress :
  IslarisContractCorrect decodeItemEntry returnAddress
    (decodeItemSelectedModelRegisters returnAddress) ->
  IslarisContractCorrect decodeItemEntry returnAddress
    (decodeItemSelectedModel returnAddress).
Proof.
  intros Hcore Sigma HG HT.
  pose proof (Hcore Sigma HG HT) as Hnative.
  unfold IslarisContractSpec, decodeItemSelectedModelRegisters, decodeItemResourcesRegisters in Hnative; cbn in Hnative.
  change (⊢ decodeItemSelectedCode -∗ ∀ args : DecodeItemArgs,
    instr_body decodeItemEntry
      (decodeItemEntryResources (decodeItemDomainAt returnAddress decodeItemC1BDomain) args ∗
       instr_pre returnAddress (∃ after : DecodeItemOutcome,
         ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
           DecodeMeaningModuloKnownBugs args after⌝ ∗ decodeItemExitResources args after)))%I.
  iIntros "Hcode" (args).
  iPoseProof (Hnative with "Hcode") as "Hbody".
  iSpecialize ("Hbody" $! args).
  iApply (instr_pre_wand with "Hbody []"); [done|done|].
  iIntros "[Hentry Hreturn]". iFrame "Hentry".
  iApply (instr_pre_wand with "Hreturn []"); [done|done|].
  iIntros "Hafter". iDestruct "Hafter" as (after) "[%Hallowed Hexit]". iExists after. iFrame "%".
  iApply (decodeItemRegisterExitWeakens with "Hexit").
Qed.

Lemma decodeItemRegisterComplianceFrames returnAddress :
  IslarisContractCorrect decodeItemEntry returnAddress
    (decodeItemSelectedModelRegisters returnAddress) ->
  IslarisContractCorrect decodeItemEntry returnAddress
    (decodeItemSelectedModelCompositional returnAddress).
Proof.
  intros Hcore Sigma HG HT.
  pose proof (Hcore Sigma HG HT) as Hnative.
  unfold IslarisContractSpec, decodeItemSelectedModelRegisters, decodeItemResourcesRegisters in Hnative; cbn in Hnative.
  change (⊢ decodeItemSelectedCode -∗ ∀ args : DecodeItemCompositionalArgs,
    instr_body decodeItemEntry
      (decodeItemEntryResourcesCompositional
         (decodeItemDomainAt returnAddress decodeItemC1BDomain) args ∗
       instr_pre returnAddress (∃ after : DecodeItemOutcome,
         ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain
             (decodeItemCompositionalBase args) /\
           DecodeMeaningModuloKnownBugs (decodeItemCompositionalBase args) after⌝ ∗
         decodeItemExitResourcesCompositional args after)))%I.
  iIntros "Hcode" (args).
  iPoseProof (Hnative with "Hcode") as "Hbody".
  iSpecialize ("Hbody" $! (decodeItemCompositionalBase args)).
  iApply (instr_pre_wand with "Hbody []"); [done|done|].
  rewrite /decodeItemEntryResourcesCompositional.
  iIntros "[[Hentry Hrest] Hreturn]". iFrame "Hentry".
  iApply (instr_pre_wand with "Hreturn [Hrest]"); [done|done|].
  iIntros "Hafter". iDestruct "Hafter" as (after) "[%Hallowed Hexit]". iExists after. iFrame "%".
  rewrite /decodeItemExitResourcesCompositional. iFrame.
Qed.
