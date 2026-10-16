Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Compliance.DecodeItemCompositionalCompliance.
Open Scope Z_scope.

(* This is the exact existential state from the call-aware table renderer. *)
Definition NextUint64CallState800d62b4 `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  let model := decodeItemSelectedModelCompositional 0x800d62b8 in
  let resources := islarisContractResources DecodeItemCompositionalArgs
    DecodeItemOutcome model Sigma _ _ in
  (∃ args : DecodeItemCompositionalArgs,
    islarisEntry DecodeItemCompositionalArgs DecodeItemOutcome resources args ∗
    instr_pre 0x800d62b8 (∃ outcome : DecodeItemOutcome,
      ⌜islarisContractAllows DecodeItemCompositionalArgs DecodeItemOutcome model args outcome⌝ ∗
      islarisExit DecodeItemCompositionalArgs DecodeItemOutcome resources args outcome))%I.

Lemma nextUint64CalleeInstallation `{!islaG Sigma} `{!threadG} :
  nextUint64SelectedCode -∗
  □ instr_pre 0x800d6960 NextUint64CallState800d62b4.
Proof.
  rewrite /nextUint64SelectedCode
    /ZesuSsz.Contracts.DecodeItemSelected.decodeItemSelectedCode.
  iIntros "[_ #Hcode]".
  iModIntro. iApply instr_pre_to_body. iNext.
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "Hstate".
  iEval (unfold NextUint64CallState800d62b4) in "Hstate".
  iDestruct "Hstate" as (args) "[Hentry Hreturn]".
  pose proof (decodeItemSelectedComplianceCompositional 0x800d62b8 Sigma islaG0 H)
    as Hcorrect.
  unfold IslarisContractSpec in Hcorrect.
  cbn [decodeItemSelectedModelCompositional decodeItemResourcesCompositional]
    in Hcorrect.
  iPoseProof (Hcorrect with "Hcode") as "Hbody".
  iSpecialize ("Hbody" $! args).
  iEval (rewrite {1}instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply ("Hbody" with "[$Hentry $Hreturn]").
Qed.
