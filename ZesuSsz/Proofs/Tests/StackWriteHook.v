Require Import ZesuSsz.Automation.All.
From iris.proofmode Require Import environments.
Require Import isla.riscv64.riscv64.

Definition stack_test_extent : Z := 16.
Definition stack_test_bounds (sp : Z) : Prop :=
  stack_test_extent <= sp /\ sp < 2 ^ 64.

Section tests.
  Context `{!islaG Sigma}.

  Lemma stack_write_disabled (sp : Z) :
    (sp - 16) ↦ₘ? 16 -∗
    find_in_context
      (FindMemMapsTo (bv_unsigned (Z_to_bv 64 sp + Z_to_bv 64 (-16) + BV 64 8)))
      (fun _ => True%I).
  Proof.
    iStartProof. iIntros "Hframe".
    Fail zesu_stack_write_if_enabled.
    iExists (MKUninit (sp - 16) 16).
    iSplitL "Hframe"; [iExact "Hframe" | done].
  Qed.

  Local Instance stack_write_enabled : ZesuStepStackWrite := I.

  Lemma stack_write_select (sp : Z) (Hsp : 16 <= sp < 2 ^ 64) :
    (sp - 16) ↦ₘ? 16 -∗
    find_in_context
      (FindMemMapsTo (bv_unsigned (Z_to_bv 64 sp + Z_to_bv 64 (-16) + BV 64 8)))
      (fun mk => match mk with
       | MKUninit start count =>
           ⌜start <= sp - 8 /\ sp - 8 + 8 <= start + count⌝ ∗
           (start ↦ₘ? count -∗ True)
       | _ => False
       end)%I.
  Proof.
    iStartProof. iIntros "Hframe".
    zesu_stack_write_if_enabled.
    iSplit; [iPureIntro; lia | iIntros "Hframe"; done].
  Qed.

  Lemma stack_write_other_frame (sp : Z) (Hsp : 32 <= sp < 2 ^ 64) :
    (sp - 32) ↦ₘ? 32 -∗
    find_in_context
      (FindMemMapsTo (bv_unsigned (Z_to_bv 64 sp + Z_to_bv 64 (-32) + BV 64 4)))
      (fun _ => True%I).
  Proof.
    iStartProof. iIntros "Hframe". zesu_stack_write_if_enabled. done.
  Qed.

  Lemma stack_write_folded_bounds (sp : Z) (Hsp : stack_test_bounds sp) :
    (sp - stack_test_extent) ↦ₘ? stack_test_extent -∗
    find_in_context
      (FindMemMapsTo (bv_unsigned (Z_to_bv 64 sp + Z_to_bv 64 (-16) + BV 64 8)))
      (fun _ => True%I).
  Proof.
    iStartProof. iIntros "Hframe". zesu_stack_write_if_enabled. done.
  Qed.

  Lemma stack_write_environment_alias (sp : Z) (Hsp : stack_test_bounds sp) :
    (sp - stack_test_extent) ↦ₘ? stack_test_extent -∗
    find_in_context
      (FindMemMapsTo (bv_unsigned (Z_to_bv 64 sp + Z_to_bv 64 (-16) + BV 64 8)))
      (fun _ => True%I).
  Proof.
    iStartProof. iIntros "Hframe".
    lazymatch goal with |- envs_entails ?context ?goal =>
      pose (stackContext := context); change (envs_entails stackContext goal)
    end.
    zesu_stack_write_if_enabled. done.
  Qed.

  Lemma stack_write_anonymous_frame (sp : Z) (Hsp : stack_test_bounds sp) :
    (sp - stack_test_extent) ↦ₘ? stack_test_extent -∗
    find_in_context
      (FindMemMapsTo (bv_unsigned (Z_to_bv 64 sp + Z_to_bv 64 (-16) + BV 64 8)))
      (fun _ => True%I).
  Proof.
    iStartProof. iIntros "?". zesu_stack_write_if_enabled. done.
  Qed.

  Lemma stack_write_reject_outside (sp : Z) (Hsp : 16 <= sp < 2 ^ 64 - 8) :
    (sp - 16) ↦ₘ? 16 -∗
    find_in_context
      (FindMemMapsTo (bv_unsigned (Z_to_bv 64 sp + BV 64 8)))
      (fun _ => True%I).
  Proof.
    iStartProof. iIntros "Hframe".
    Fail zesu_stack_write_if_enabled.
    iExists (MKUninit (sp - 16) 16).
    iSplitL "Hframe"; [iExact "Hframe" | done].
  Qed.
End tests.
