Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import IslaTraces.write_success_113.a15930_spec.
Require Import IslaTraces.write_success_113.a15934_spec.
Require Import IslaTraces.write_success_113.a15938.

Lemma write_success_post_15930_load_pointer
    `{!islaG Sigma} `{!threadG} :
  instr 0x15930 (Some IslaTraces.write_success_113.a15930.a15930) -∗
  instr_body 0x15930
    (InstrSpecs.Specs.zesu_ld_spec 0x15930 "x10" "x2" 24).
Proof.
  iIntros "Hinstr".
  iApply (IslaTraces.write_success_113.a15930_spec.a15930_spec
    0x15930 with "Hinstr").
Qed.

Definition writeSuccessPost15938Spec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ: (fun r1 => ⌜valu_has_shape r1 (BitsShape 64)⌝) ∗
   Q ∗
   instr_pre 0x1593c
     (reg_col zesu_ram_sys_regs ∗
      "x1" ↦ᵣ RVal_Bits (BV 64 0x15938) ∗ Q) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessPost15938Spec) := I.

Lemma write_success_post_15938_auipc
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr 0x15938 (Some IslaTraces.write_success_113.a15938.a15938) -∗
  instr_body 0x15938 (writeSuccessPost15938Spec Q).
Proof.
  iStartProof. iIntros "Hinstr".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  Unshelve. all: iFrame.
Qed.

Lemma write_success_post_15934_load_count
    `{!islaG Sigma} `{!threadG} :
  instr 0x15934 (Some IslaTraces.write_success_113.a15934.a15934) -∗
  instr_body 0x15934
    (InstrSpecs.Specs.zesu_ld_spec 0x15934 "x11" "x2" 16).
Proof.
  iIntros "Hinstr".
  iApply (IslaTraces.write_success_113.a15934_spec.a15934_spec
    0x15934 with "Hinstr").
Qed.
