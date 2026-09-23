Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SpecTable.
Require Import ZesuSsz.Automation.MarkedRawInstruction.
Require Import ZesuSsz.Automation.Switches.MarkedRawInstruction.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.

Local Instance marked_raw_at_159a0 :
    ZesuRawInstructionAt Index.lookup 0x159a0.
Proof. unfold ZesuRawInstructionAt. rewrite Index.lookup_a159a0. eexists. reflexivity. Qed.

Definition sealed_tf2_array `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (words : list (bv 64)) : iProp Sigma :=
  ((bv_unsigned sp + 96) ↦ₘ∗ words)%I.
Lemma sealed_tf2_array_unfold `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (words : list (bv 64)) :
  sealed_tf2_array sp words ⊣⊢ ((bv_unsigned sp + 96) ↦ₘ∗ words)%I.
Proof. done. Qed.
Global Opaque sealed_tf2_array.

Lemma marked_raw_tf2_preserves_array `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (words : list (bv 64)) :
  instr_lookup_resources Index.lookup -∗
  Index.spec_instr_resources -∗
  sealed_tf2_array sp words -∗
  find_in_context (FindInstrKind 0x159a0 false)
    (fun kind => match kind with
      | IKInstr (Some _) => sealed_tf2_array sp words
      | _ => False%I
      end).
Proof.
  iStartProof. iIntros "#Hraw #Htable Hframe".
  zesu_run.
Qed.

Print Assumptions marked_raw_tf2_preserves_array.
