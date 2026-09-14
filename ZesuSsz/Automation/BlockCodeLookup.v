Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.

Lemma instr_lookup_collect_blocks `{!islaG Sigma} `{!threadG}
    (lookup : Z -> option isla_trace) (blocks : list (list (Z * isla_trace))) :
  Forall (fun block => Forall (fun instruction =>
    lookup instruction.1 = Some instruction.2) block) blocks ->
  instr_lookup_resources lookup -∗
  ([∗ list] block ∈ blocks,
    [∗ list] instruction ∈ block, instr instruction.1 (Some instruction.2))%I.
Proof.
  intros Hblocks. induction Hblocks as [|block blocks Hblock Hblocks IH].
  - iIntros "#Hcode". done.
  - iIntros "#Hcode". rewrite big_sepL_cons. iSplit.
    + iApply (instr_lookup_collect lookup block Hblock with "Hcode").
    + iApply (IH with "Hcode").
Qed.
Print Assumptions instr_lookup_collect_blocks.
