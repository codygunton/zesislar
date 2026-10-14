Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
From iris.proofmode Require Import environments.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.

Section tests.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma selected_lookup_remains_named (instructions : list (Z * isla_trace)) :
    instr_lookup_resources (selectedCodeLookup instructions) -∗
    instr_lookup_resources (selectedCodeLookup instructions).
  Proof.
    iStartProof. iIntros "Hcode". liSimpl.
    lazymatch goal with
    | |- envs_entails _ (instr_lookup_resources (selectedCodeLookup instructions)) => idtac
    end.
    iExact "Hcode".
  Qed.

  Lemma selected_lookup_generated_table_remains_named :
    instr_lookup_resources (selectedCodeLookup instr_map) -∗
    instr_lookup_resources (selectedCodeLookup instr_map).
  Proof.
    iStartProof. iIntros "Hcode". liSimpl.
    lazymatch goal with
    | |- envs_entails _ (instr_lookup_resources (selectedCodeLookup instr_map)) => idtac
    end.
    iExact "Hcode".
  Qed.
  Lemma selected_lookup_native_resolution :
    instr_lookup_resources (selectedCodeLookup instr_map) -∗
    find_in_context (FindInstrKind 0x800d6a24 false) (fun _ => True%I).
  Proof.
    iStartProof. iIntros "#Hcode". repeat zesu_liAStep.
  Qed.
End tests.

Lemma selected_lookup_explicit_instruction :
  selectedCodeLookup instr_map 0x800d6a24 = Some a800d6a24.
Proof. vm_compute. reflexivity. Qed.

Lemma selected_lookup_explicit_gap :
  selectedCodeLookup instr_map 0 = None.
Proof. vm_compute. reflexivity. Qed.
