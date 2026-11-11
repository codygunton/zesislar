(* The decodeItem compliance theorems over the 24 generated block proofs.
   The composition is in DecodeItemGeneratedComposition.v. This module holds
   only the two public statements: the soundness gate restates each lemma of a
   PUBLIC module at the top level after its own source, so the module keeps no
   other proof. DecodeItemCompliance.v derives the production theorem from it. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Compliance.DecodeItemGeneratedComposition.
Local Open Scope Z_scope.

(* ---- The registers statement and its weakening to the reviewed model. ---- *)
Lemma decodeItemGeneratedComplianceRegisters :
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemSelectedModelRegisters returnAddress).
Proof.
  intros returnAddress Sigma HG HT.
  change (⊢ decodeItemSelectedCode -∗ ∀ args : DecodeItemArgs,
    instr_body decodeItemEntry
      (decodeItemEntryResources (decodeItemDomainAt returnAddress decodeItemC1BDomain) args ∗
       instr_pre returnAddress (∃ after : DecodeItemOutcome,
         ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
           DecodeMeaningModuloKnownBugs args after⌝ ∗
         decodeItemExitResourcesRegisters args after)))%I.
  exact (@fp301_registers_body Sigma HG HT returnAddress).
Qed.

Lemma decodeItemGeneratedCompliance :
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemSelectedModel returnAddress).
Proof.
  intros returnAddress Sigma HG HT.
  pose proof (decodeItemGeneratedComplianceRegisters returnAddress Sigma HG HT) as Hnative.
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
  iApply (fp301_register_exit_weakens with "Hexit").
Qed.
