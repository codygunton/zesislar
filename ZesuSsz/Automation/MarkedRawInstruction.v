(* Select the raw trace at one marked PC. Other PCs keep their table entry. *)
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Lookup.

Class ZesuRawInstructionAt (lookup : Z -> option isla_trace)
    (address : Z) : Prop :=
  zesu_raw_instruction_exists : is_Some (lookup address).

Section marked_raw_instruction.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma find_in_context_zesu_marked_raw address lookup later continuation
      `{!ZesuRawInstructionAt lookup address} :
    (instr_lookup_resources lookup ∗
      continuation (IKInstr (lookup address))) ⊢
    find_in_context (FindInstrKind address later) continuation.
  Proof.
    iIntros "[#Hcode Hcontinuation]".
    iApply find_in_context_instr_lookup_resources.
    iExists lookup. iFrame "Hcode Hcontinuation".
    iPureIntro. exact zesu_raw_instruction_exists.
  Qed.

  Definition find_in_context_zesu_marked_raw_inst address :=
    [instance find_in_context_zesu_marked_raw address with FICSyntactic].
  Global Existing Instance find_in_context_zesu_marked_raw_inst | 9.
End marked_raw_instruction.

Print Assumptions find_in_context_zesu_marked_raw.
