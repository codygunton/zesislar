Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export IslaTraces.write_success_88.a15680.
Require Import InstrSpecs.Specs.

Definition a15680_addi_spec `{!islaG Σ} `{!threadG} (pc : Z) : iProp Σ :=
  ∃ src : bv 64,
  reg_col zesu_sys_regs ∗
  "x9" ↦ᵣ RVal_Bits src ∗
  "x10" ↦ᵣ: (fun _ => True)%I ∗
  instr_pre (pc + 4) (
    reg_col zesu_sys_regs ∗
    "x9" ↦ᵣ RVal_Bits src ∗
    "x10" ↦ᵣ RVal_Bits src ∗ True).
Global Instance : LithiumUnfold (@a15680_addi_spec) := I.

Lemma a15680_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a15680)
  ⊢ instr_body pc (a15680_addi_spec pc).
Proof.
  iStartProof.
  repeat liAStep.
  Unshelve. all: prepare_sidecond.
  all: (try bv_solve; try lia).
Qed.

Definition a15680_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a15680_spec pc).
Global Existing Instance a15680_spec_inst.
