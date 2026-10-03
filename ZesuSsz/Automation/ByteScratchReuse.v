Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
From iris.proofmode Require Import environments.

(* Keep the initialized prefix when the caller requests its full scratch. *)
Ltac zesu_initialized_byte_scratch_tail :=
  let _ := constr:(_ : ZesuStepArrayLoadPriority) in
  lazymatch goal with
  | |- envs_entails _
      (subsume (?source ↦ₘ∗ ?bytes)
        (fun _ : ?A => ?target ↦ₘ? 48) ?G)%I =>
      let kind := type of bytes in
      constr_eq kind (list (bv 8));
      iApply (subsume_mem_byte_array_8_uninit A source target bytes 48 G)
  end.
