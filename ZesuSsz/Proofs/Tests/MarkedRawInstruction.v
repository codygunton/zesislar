Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SpecTable.
Require Import ZesuSsz.Automation.MarkedRawInstruction.
Require Import ZesuSsz.Automation.Switches.MarkedRawInstruction.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.

Local Instance marked_raw_at_156e8 :
    ZesuRawInstructionAt Index.lookup 0x156e8.
Proof. unfold ZesuRawInstructionAt. rewrite Index.lookup_a156e8. eexists. reflexivity. Qed.

Definition sealed_array_frame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (words : list (bv 64)) : iProp Sigma :=
  ((bv_unsigned sp + 1032) ↦ₘ∗ words)%I.
Lemma sealed_array_frame_unfold `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (words : list (bv 64)) :
  sealed_array_frame sp words ⊣⊢ ((bv_unsigned sp + 1032) ↦ₘ∗ words)%I.
Proof. done. Qed.
Global Opaque sealed_array_frame.

Lemma marked_raw_preserves_sealed_array `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (words : list (bv 64)) :
  instr_lookup_resources Index.lookup -∗
  Index.spec_instr_resources -∗
  sealed_array_frame sp words -∗
  find_in_context (FindInstrKind 0x156e8 false)
    (fun kind => match kind with
      | IKInstr (Some _) => sealed_array_frame sp words
      | _ => False%I
      end).
Proof.
  iStartProof. iIntros "#Hraw #Htable Hframe".
  zesu_run.
Qed.

Print Assumptions marked_raw_preserves_sealed_array.

Lemma unmarked_instruction_uses_table `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources Index.lookup -∗
  Index.spec_instr_resources -∗
  find_in_context (FindInstrKind 0x156f0 false)
    (fun kind => match kind with
      | IKPre false _ => True%I
      | _ => False%I
      end).
Proof.
  iStartProof. iIntros "#Hraw #Htable".
  zesu_run.
Qed.

Print Assumptions unmarked_instruction_uses_table.
