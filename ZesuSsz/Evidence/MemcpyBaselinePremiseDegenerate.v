From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Automation2.Calls.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.

Open Scope Z_scope.
Set Default Proof Mode "Classic".

(* The memcpy premise of the reviewed baseline d73a7a5a5, copied verbatim
   from ZesuSsz/Contracts/ParentHeaderMemcpyService.v at that commit.
   It is not a premise of any current theorem. This file shows that it is
   degenerate: instr_pre is contravariant in its precondition, and the
   precondition is a wand whose argument owns x1, x10, x11 and x12. Any
   resource that owns one of those registers proves the wand by register
   exclusivity. *)
Definition baselineRuntimeBytesAt (state : ZiskRuntimeState unit)
    (address : Z) (count : nat) : list byte :=
  List.map (fun offset => Z_to_bv 8
    (ziskRuntimeMemory state (address + Z.of_nat offset)))
    (List.seq 0 count).

Definition baselineMemcpyServiceEntry `{!islaG Sigma} `{!threadG}
    (permissions : ZiskRuntimePermissions) (destination returnAddress : Z)
    (before : ZiskRuntimeState unit) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 destination) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 parentHeaderMemcpySource) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 parentHeaderMemcpyLength) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 returnAddress) ∗
   parentHeaderMemcpySource ↦ₘ∗
     baselineRuntimeBytesAt before parentHeaderMemcpySource 80 ∗
   destination ↦ₘ∗ baselineRuntimeBytesAt before destination 80 ∗
   ziskExtraParamsAddress ↦ₘ∗
     baselineRuntimeBytesAt before ziskExtraParamsAddress 8 ∗
   ⌜ziskMemcpyEntry permissions memcpyCsrPc
      (parentHeaderMemcpyArguments destination returnAddress) before⌝ ∗
   True)%I.

Definition baselineMemcpyServiceExit `{!islaG Sigma} `{!threadG}
    (destination returnAddress : Z) (after : ZiskRuntimeState unit) :
    iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 destination) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 parentHeaderMemcpySource) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 parentHeaderMemcpyLength) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 returnAddress) ∗
   parentHeaderMemcpySource ↦ₘ∗
     baselineRuntimeBytesAt after parentHeaderMemcpySource 80 ∗
   destination ↦ₘ∗ baselineRuntimeBytesAt after destination 80 ∗
   ziskExtraParamsAddress ↦ₘ∗
     baselineRuntimeBytesAt after ziskExtraParamsAddress 8 ∗
   True)%I.

Definition baselineMemcpyServiceInstrSpec `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (∀ (permissions : ZiskRuntimePermissions) (destination returnAddress : Z)
     (before : ZiskRuntimeState unit),
     baselineMemcpyServiceEntry permissions destination returnAddress before -∗
     instr_pre (Z.land returnAddress (-2))
       (∃ after : ZiskRuntimeState unit,
          ⌜ziskMemcpyAllows selectedMemcpy permissions
             (parentHeaderMemcpyArguments destination returnAddress)
             before after⌝ ∗
          baselineMemcpyServiceExit destination returnAddress after))%I.

Definition baselineMemcpyServicePremise `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (□ instr_pre memcpyCsrPc baselineMemcpyServiceInstrSpec)%I.

(* Reaching memcpy with x10 alone, and no return continuation, is "safe". *)
Lemma baselineMemcpyServicePremise_degenerate `{!islaG Sigma} `{!threadG}
    (value : valu) :
  baselineMemcpyServicePremise ⊢ □ instr_pre memcpyCsrPc ("x10" ↦ᵣ value).
Proof.
  iIntros "#Hpremise !>".
  iApply (instr_pre_wand with "Hpremise"); [done | done |].
  iIntros "Hx10" (permissions destination returnAddress before) "Hentry".
  iDestruct "Hentry" as "(_ & Hentry10 & _)".
  rewrite reg_mapsto_eq /reg_mapsto_def.
  by iDestruct (ghost_map_elem_ne with "Hx10 Hentry10") as %Hne.
Qed.

(* The same holds for the corrected premise's precondition, so the
   baseline premise implies it without saying anything about memcpy. *)
Lemma baselineMemcpyServicePremise_implies_any_call `{!islaG Sigma} `{!threadG} :
  baselineMemcpyServicePremise ⊢ memcpyCallPremise.
Proof.
  iIntros "#Hpremise !>".
  iApply (instr_pre_wand with "Hpremise"); [done | done |].
  iIntros "Hcall" (permissions destination returnAddress before) "Hentry".
  iDestruct "Hentry" as "(_ & Hentry10 & _)".
  rewrite /memcpyCallSpec2 /machine_call.
  iDestruct "Hcall" as (sp ret) "(_ & _ & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "[Hx10 _]".
  rewrite reg_mapsto_eq /reg_mapsto_def.
  by iDestruct (ghost_map_elem_ne with "Hx10 Hentry10") as %Hne.
Qed.
