Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.EntryIntro.
Require Import ZesuSsz.Automation.Switches.ReturnRoute.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Stock.Closure.a800e06c8.
From Coq Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition r3_memcpy_ret_entry `{!islaG Sigma} `{!threadG}
    (ret : bv 64) : iProp Sigma :=
  ("x1" ↦ᵣ RVal_Bits ret ∗ ⌜(bv_unsigned ret mod 4 = 0)%Z⌝ ∗
   reg_col zesu_sys_regs ∗
   instr_pre (bv_unsigned ret) True ∗ True)%I.
Global Instance : LithiumUnfold (@r3_memcpy_ret_entry) := I.
Global Typeclasses Opaque r3_memcpy_ret_entry.

Lemma r3_memcpy_ret_no_frame `{!islaG Sigma} `{!threadG} (ret : bv 64) :
  instr 0x800e06c8 (Some ZesuSsz.Stock.Closure.a800e06c8.a800e06c8) -∗
  instr_body 0x800e06c8 (r3_memcpy_ret_entry ret).
Proof.
zesu_block.
Qed.

Lemma r3_synthetic_no_frame `{!islaG Sigma} `{!threadG}
    (pc : Z) (ret : bv 64) :
  instr pc (Some ZesuSsz.Stock.Closure.a800e06c8.a800e06c8) -∗
  instr_body pc (
    reg_col zesu_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
    ⌜(bv_unsigned ret mod 4 = 0)%Z⌝ ∗
    instr_pre (bv_unsigned ret)
      (reg_col zesu_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗ True) ∗ True).
Proof.
zesu_block.
Qed.

Lemma r3_unknown_x1 `{!islaG Sigma} `{!threadG}
    (pc : Z) (returnAddress : Z) : True.
Proof.
Fail assert (Htest : (⊢ instr pc (Some ZesuSsz.Stock.Closure.a800e06c8.a800e06c8) -∗
  instr_body pc (
    reg_col ((KindReg "x1", BitsShape 64) :: zesu_sys_regs) ∗
    instr_pre returnAddress
      (reg_col ((KindReg "x1", BitsShape 64) :: zesu_sys_regs) ∗ True) ∗ True))%I) by solve [zesu_block].
exact I.
Qed.

Lemma r3_misaligned_frame `{!islaG Sigma} `{!threadG}
    (pc frameBase : Z) (frameBytes : list (bv 8)) : True.
Proof.
Fail assert (Htest : (⊢ instr pc (Some ZesuSsz.Stock.Closure.a800e06c8.a800e06c8) -∗
  instr_body pc (
    reg_col zesu_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 frameBytes)))) ∗
    frameBase ↦ₘ∗ frameBytes ∗
    ⌜(length frameBytes = 16)%nat⌝ ∗
    ⌜(bv_unsigned (Z_to_bv 64
      (little_endian_to_bv 8 (take 8 (drop 8 frameBytes)))) mod 4 = 2)%Z⌝ ∗
    instr_pre (bv_unsigned (Z_to_bv 64
      (little_endian_to_bv 8 (take 8 (drop 8 frameBytes)))))
      (reg_col zesu_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits
         (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 frameBytes)))) ∗
       frameBase ↦ₘ∗ frameBytes ∗ True) ∗ True))%I) by solve [zesu_block].
exact I.
Qed.

(* The source remains intact when the second source-keyed class contributes facts. *)
Definition r3_exit_control_source {Sigma} (facts : Prop)
    (resource : iProp Sigma) : iProp Sigma := (⌜facts⌝ ∗ resource)%I.
Global Instance : LithiumUnfold (@r3_exit_control_source) := I.
Global Typeclasses Opaque r3_exit_control_source.
Definition r3_exit_control_wrapper {Sigma} (facts : Prop)
    (resource frame : iProp Sigma) : iProp Sigma :=
  (r3_exit_control_source facts resource ∗ frame)%I.
Global Instance : LithiumUnfold (@r3_exit_control_wrapper) := I.
Global Typeclasses Opaque r3_exit_control_wrapper.
#[local] Instance r3_exit_control_evidence {Sigma} (facts : Prop)
    (resource : iProp Sigma) :
  ZesuExitMeaning (r3_exit_control_source facts resource) facts.
Proof. rewrite /ZesuExitMeaning /r3_exit_control_source. iIntros "[%Hfacts _]". done. Qed.

Lemma r3_exit_goal_control `{!islaG Sigma} `{!threadG}
    (pc : Z) (facts : Prop) (premise resource frame : iProp Sigma) :
  (premise -∗ instr_body pc (⌜facts⌝ ∗ r3_exit_control_source facts resource ∗ frame)) -∗
  premise -∗ instr_body pc (r3_exit_control_wrapper facts resource frame).
Proof.
zesu_entry_intro_goal_if_enabled.
lazymatch goal with
| _ : @ZesuExitMeaningApplied Sigma (r3_exit_control_source facts resource) facts
      (@r3_exit_control_evidence Sigma facts resource) |- _ => idtac
end.
change (⊢ (premise -∗ instr_body pc (⌜facts⌝ ∗ r3_exit_control_source facts resource ∗ frame)) -∗
  premise -∗ instr_body pc (⌜facts⌝ ∗ r3_exit_control_source facts resource ∗ frame))%I.
iStartProof. iIntros "Hbody Hpremise". iApply ("Hbody" with "Hpremise").
Qed.
Print Assumptions r3_exit_goal_control.

(* Both source-keyed classes contribute once for a shared source. *)
#[local] Instance r3_dual_entry_on : ZesuStepEntryIntro := {}.
Definition r3_dual_source {Sigma} (left right : Prop)
    (resource : iProp Sigma) : iProp Sigma := (⌜left /\ right⌝ ∗ resource)%I.
Global Instance : LithiumUnfold (@r3_dual_source) := I.
Global Typeclasses Opaque r3_dual_source.
Definition r3_dual_wrapper {Sigma} (left right : Prop)
    (resource frame : iProp Sigma) : iProp Sigma :=
  (r3_dual_source left right resource ∗ frame)%I.
Global Instance : LithiumUnfold (@r3_dual_wrapper) := I.
Global Typeclasses Opaque r3_dual_wrapper.
#[local] Instance r3_dual_entry_evidence {Sigma} (left right : Prop)
    (resource : iProp Sigma) :
  ZesuEntryIntro (r3_dual_source left right resource) left.
Proof. rewrite /ZesuEntryIntro /r3_dual_source. iIntros "[%Hp _]". iPureIntro. tauto. Qed.
#[local] Instance r3_dual_exit_evidence {Sigma} (left right : Prop)
    (resource : iProp Sigma) :
  ZesuExitMeaning (r3_dual_source left right resource) right.
Proof. rewrite /ZesuExitMeaning /r3_dual_source. iIntros "[%Hp _]". iPureIntro. tauto. Qed.

Lemma r3_dual_source_control `{!islaG Sigma} `{!threadG}
    (pc : Z) (left right : Prop) (premise resource frame : iProp Sigma) :
  (premise -∗ instr_body pc
    (⌜left /\ right⌝ ∗ r3_dual_source left right resource ∗ frame)) -∗
  premise -∗ instr_body pc (r3_dual_wrapper left right resource frame).
Proof.
zesu_entry_intro_goal_if_enabled.
lazymatch goal with
| _ : @ZesuEntryIntroApplied Sigma (r3_dual_source left right resource) left
      (@r3_dual_entry_evidence Sigma left right resource) |- _ => idtac
end.
lazymatch goal with
| _ : @ZesuExitMeaningApplied Sigma (r3_dual_source left right resource) right
      (@r3_dual_exit_evidence Sigma left right resource) |- _ => idtac
end.
Fail zesu_entry_intro_goal_if_enabled.
change (⊢ (premise -∗ instr_body pc
    (⌜left /\ right⌝ ∗ r3_dual_source left right resource ∗ frame)) -∗
  premise -∗ instr_body pc
    (⌜left /\ right⌝ ∗ r3_dual_source left right resource ∗ frame))%I.
iStartProof. iIntros "Hbody Hpremise". iApply ("Hbody" with "Hpremise").
Qed.
Print Assumptions r3_dual_source_control.
