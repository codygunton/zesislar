Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export IslaTraces.write_success_88.a15684.
Require Import InstrSpecs.Specs.

Definition a15684_auipc_spec `{!islaG Σ} `{!threadG} (pc : Z) : iProp Σ :=
  reg_col zesu_sys_regs ∗
  "x1" ↦ᵣ: (fun _ => True)%I ∗
  instr_pre (pc + 4) (
    reg_col zesu_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 pc) ∗ True).
Global Instance : LithiumUnfold (@a15684_auipc_spec) := I.

Lemma a15684_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a15684)
  ⊢ instr_body pc (a15684_auipc_spec pc).
Proof.
  iStartProof.
  repeat liAStep.
  Unshelve. all: prepare_sidecond.
  all: (try bv_solve; try lia).
Qed.

Definition a15684_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a15684_spec pc).
Global Existing Instance a15684_spec_inst.
