(* Select the raw trace at one marked PC. Other PCs keep their table entry. *)
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Lookup.
From iris.proofmode Require Import environments.

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

End marked_raw_instruction.

Print Assumptions find_in_context_zesu_marked_raw.

Class ZesuStepMarkedRawInstruction : Prop := zesu_step_marked_raw_instruction : True.

Ltac zesu_select_marked_raw_if_enabled :=
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindInstrKind ?address ?later) ?continuation) =>
      let _ := constr:(_ : ZesuStepMarkedRawInstruction) in
      let marker := constr:(_ : ZesuRawInstructionAt _ address) in
      lazymatch type of marker with
      | ZesuRawInstructionAt ?lookup _ =>
          iApply (find_in_context_zesu_marked_raw address lookup later continuation)
      end
  end.
