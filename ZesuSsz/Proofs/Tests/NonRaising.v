Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
From IslaTraces.write_success_32 Require Import a15048.

Lemma test_nonraising_live_pure (n : nat) : n + 0 = n.
Proof. zesu_block. Qed.
Print Assumptions test_nonraising_live_pure.

Definition nonraising_live_wrapper (n : nat) := n.
Lemma test_nonraising_live_unfold (n : nat) : nonraising_live_wrapper n = n.
Proof. zesu_block. Qed.
Print Assumptions test_nonraising_live_unfold.

(* assert_succeeds runs a disposable proof state. The unknown proposition
   must remain visible; solve must not report a false closure. *)
Lemma test_nonraising_live_residual (P : Prop) : True.
Proof.
  assert_succeeds (assert P; [
    tryif solve [zesu_block] then fail 1 "false closure" else
      (zesu_block; lazymatch goal with |- P => idtac end)
    | idtac]).
  exact I.
Qed.
Print Assumptions test_nonraising_live_residual.

Lemma test_nonraising_live_iris `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  P -∗ P.
Proof. zesu_block. Qed.
Print Assumptions test_nonraising_live_iris.

Lemma test_nonraising_live_iris_residual `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : True.
Proof.
  assert_succeeds (assert (True%I ⊢ P); [
    tryif solve [zesu_block] then fail 1 "false Iris closure" else zesu_block
    | idtac]).
  exact I.
Qed.
Print Assumptions test_nonraising_live_iris_residual.

#[local] Hint Rewrite zesu_bv_sign_extend_same : isla_coq_rewrite.
#[local] Hint Rewrite zesu_bv_unsigned_add_Z_64 using bv_solve
  : isla_coq_rewrite lithium_rewrite.
#[local] Hint Rewrite zesu_bv_unsigned_add_no_wrap_64 using bv_solve
  : isla_coq_rewrite lithium_rewrite.

Lemma test_nonraising_live_machine_load `{!islaG Sigma} `{!threadG}
    (base : bv 64) (bytes : list (bv 8))
    (Hlength : length bytes = 288%nat) :
  instr 0x15048 (Some a15048) -∗
  instr_body 0x15048 (
    reg_col zesu_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits base ∗
    "x16" ↦ᵣ: (fun _ => True) ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned base ∧
      bv_unsigned base + 288 <= (machineRamEnd defaultMap)⌝ ∗
    bv_unsigned base ↦ₘ∗ bytes ∗
    instr_pre 0x1504c (
      reg_col zesu_sys_regs ∗
      "x10" ↦ᵣ RVal_Bits base ∗
      "x16" ↦ᵣ RVal_Bits
        (Z_to_bv 64
          (little_endian_to_bv 8 (take 8 (drop 80 bytes)))) ∗
      bv_unsigned base ↦ₘ∗ bytes ∗ True) ∗ True).
Proof. zesu_block. Qed.

Print Assumptions test_nonraising_live_machine_load.
