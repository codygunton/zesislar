Require Import ZesuSsz.Automation.All.
Require Import InstrSpecs.Lookup.
Require Import isla.riscv64.riscv64.

Lemma instr_lookup_collect `{!islaG Sigma} `{!threadG}
    (lookup : Z -> option isla_trace) (instructions : list (Z * isla_trace)) :
  Forall (fun instruction => lookup instruction.1 = Some instruction.2) instructions ->
  instr_lookup_resources lookup -∗
  ([∗ list] instruction ∈ instructions, instr instruction.1 (Some instruction.2))%I.
Proof.
  intros Hlookup. induction Hlookup as [|[address trace] rest Heq Hrest IH].
  - iIntros "#Hcode". done.
  - iIntros "#Hcode". rewrite big_sepL_cons. iSplit; last (iApply IH; iExact "Hcode").
    iEval (rewrite /instr_lookup_resources) in "Hcode".
    iPoseProof ("Hcode" $! address with "[]") as "Hinstr".
    { iPureIntro. rewrite Heq. eauto. }
    iEval (rewrite Heq) in "Hinstr". iExact "Hinstr".
Qed.
Print Assumptions instr_lookup_collect.
