Require Import ZesuSsz.Automation.All.
Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Export IslaTraces.write_success_49.a151a0.

Definition writeSuccessTransactions151a0MvSpec
    `{!islaG Sigma} `{!threadG} (pc : Z) : iProp Sigma :=
  (∃ value : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x20" ↦ᵣ RVal_Bits value ∗
    ("x11" ↦ᵣ: (fun _ => True)%I) ∗
    instr_pre (pc + 4) (
      reg_col zesu_ram_sys_regs ∗
      "x20" ↦ᵣ RVal_Bits value ∗
      "x11" ↦ᵣ RVal_Bits value ∗ True))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions151a0MvSpec) := I.

Lemma write_success_transactions_151a0_mv_spec
    `{!islaG Sigma} `{!threadG} (pc : Z) :
  instr pc (Some IslaTraces.write_success_49.a151a0.a151a0) ⊢
  instr_body pc (writeSuccessTransactions151a0MvSpec pc).
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.

Definition writeSuccessTransactions151a0MvSpec_inst
    `{!islaG Sigma} `{!threadG} (pc : Z) :=
  entails_to_simplify_hyp 0 (write_success_transactions_151a0_mv_spec pc).

Global Existing Instance writeSuccessTransactions151a0MvSpec_inst.
