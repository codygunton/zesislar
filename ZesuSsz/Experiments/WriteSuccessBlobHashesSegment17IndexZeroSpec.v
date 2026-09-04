Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_67.a1548c.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition writeSuccessBlobHashesLbuIndexZeroSpec
    `{!islaG Sigma} `{!threadG} (pc : Z) : iProp Sigma :=
  ∃ (base : bv 64) (byte : bv 8),
  reg_col zesu_instr_sys_regs ∗
  "x21" ↦ᵣ: (fun _ => True)%I ∗
  "x19" ↦ᵣ RVal_Bits base ∗
  bv_unsigned base ↦ₘ byte ∗
  ⌜0x20000000 <= bv_unsigned base < 0x40000000⌝ ∗
  instr_pre (pc + 4) (
    reg_col zesu_instr_sys_regs ∗
    "x21" ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) ∗
    "x19" ↦ᵣ RVal_Bits base ∗
    bv_unsigned base ↦ₘ byte ∗ True) ∗ True.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesLbuIndexZeroSpec) := I.

Lemma write_success_blob_hashes_a1548c_index_zero_spec
    `{!islaG Sigma} `{!threadG} (pc : Z) :
  instr pc (Some IslaTraces.write_success_67.a1548c.a1548c) ⊢
  instr_body pc (writeSuccessBlobHashesLbuIndexZeroSpec pc).
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try lia.
Qed.
