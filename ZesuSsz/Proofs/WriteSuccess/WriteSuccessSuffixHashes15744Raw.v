Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import IslaTraces.write_success_101.a15744.

Definition writeSuccessSuffixHashes15744Spec
    `{!islaG Sigma} `{!threadG} (Q : bv 64 -> iProp Sigma) : iProp Sigma :=
  (∃ value : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x8" ↦ᵣ RVal_Bits value ∗
    "x10" ↦ᵣ: (fun r10 => ⌜valu_has_shape r10 (BitsShape 64)⌝) ∗
    Q value ∗
    instr_pre 0x15748
      (reg_col zesu_ram_sys_regs ∗
       "x8" ↦ᵣ RVal_Bits value ∗
       "x10" ↦ᵣ RVal_Bits value ∗ Q value) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashes15744Spec) := I.

Lemma write_success_suffix_hashes_15744_raw
    `{!islaG Sigma} `{!threadG} (Q : bv 64 -> iProp Sigma) :
  instr 0x15744 (Some IslaTraces.write_success_101.a15744.a15744) -∗
  instr_body 0x15744 (writeSuccessSuffixHashes15744Spec Q).
Proof.
  iStartProof. iIntros "Hinstr".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try iFrame.
  all: try (iIntros "HQ"; iExact "HQ").
  Unshelve. all: iFrame.
Qed.
