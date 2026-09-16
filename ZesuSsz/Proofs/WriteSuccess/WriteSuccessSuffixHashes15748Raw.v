Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import IslaTraces.write_success_101.a15748.

Definition writeSuccessSuffixHashes15748Spec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ: (fun r1 => ⌜valu_has_shape r1 (BitsShape 64)⌝) ∗
   Q ∗
   instr_pre 0x1574c
     (reg_col zesu_ram_sys_regs ∗
      "x1" ↦ᵣ RVal_Bits (BV 64 0x15748) ∗ Q) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashes15748Spec) := I.

Lemma write_success_suffix_hashes_15748_raw
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr 0x15748 (Some IslaTraces.write_success_101.a15748.a15748) -∗
  instr_body 0x15748 (writeSuccessSuffixHashes15748Spec Q).
Proof.
  iStartProof. iIntros "Hinstr".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  Unshelve. all: iFrame.
Qed.
