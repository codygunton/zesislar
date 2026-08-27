Require Import isla.riscv64.riscv64.
From IslaTraces.zkvm_exit Require Import instrs.
Require Import ZesuSsz.Contracts.Level1.

(** The production I/O context is below the tutorial RAM window. This register
    collection matches the focused trace-generation configuration. *)
Definition zesu_sys_regs : list (reg_kind * valu_shape) := [
  (KindReg "rv_enable_pmp", ExactShape (RVal_Bool false));
  (KindReg "rv_enable_misaligned_access", ExactShape (RVal_Bool false));
  (KindReg "rv_ram_base", ExactShape (RVal_Bits (BV 64 0x0)));
  (KindReg "rv_ram_size", ExactShape (RVal_Bits (BV 64 0x40000000)));
  (KindReg "rv_rom_base", ExactShape (RVal_Bits (BV 64 0x1000)));
  (KindReg "rv_rom_size", ExactShape (RVal_Bits (BV 64 0x100)));
  (KindReg "rv_clint_base", ExactShape (RVal_Bits (BV 64 0x2000000)));
  (KindReg "rv_clint_size", ExactShape (RVal_Bits (BV 64 0xc0000)));
  (KindReg "rv_htif_tohost", ExactShape (RVal_Bits (BV 64 0x40001000)));
  (KindReg "cur_privilege", ExactShape (RVal_Enum "Machine"));
  (KindReg "misa", ExactShape (RegVal_Struct [
    ("bits", RVal_Bits (BV 64 0x8000000000001100))]));
  (KindReg "mstatus", StructShape [("bits", MaskShape 64 0x20000 0)]);
  (KindReg "satp", BitsShape 64)
].

Lemma zkvm_exit_instruction_body `{!islaG Σ} `{!threadG}
    (code old_x5 old_exit_code : bv 64) :
  instr 0x101c4 (Some a101c4) -∗
  instr 0x101c8 (Some a101c8) -∗
  instr 0x101cc (Some a101cc) -∗
  instr_body 0x101c4 (
    reg_col zesu_sys_regs ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits code ∗
    0x2401a0d0 ↦ₘ old_exit_code ∗
    instr_pre 0x101d0 (
      reg_col zesu_sys_regs ∗
      "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
      "x10" ↦ᵣ RVal_Bits code ∗
      0x2401a0d0 ↦ₘ code ∗
      True)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: liShow.
  all: try bv_solve.
Qed.

Definition zkvm_exit_contract_resources `{!islaG Σ} `{!threadG} :
    IslarisContractResources ZkvmExitArgs unit := {|
  islarisEntry := fun args =>
    (∃ (old_x5 old_exit_code : bv 64),
      ⌜0 <= zkvmExitCode args < 2 ^ 64⌝ ∗
      reg_col zesu_sys_regs ∗
      "x5" ↦ᵣ RVal_Bits old_x5 ∗
      "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (zkvmExitCode args)) ∗
      0x2401a0d0 ↦ₘ old_exit_code)%I;
  islarisExit := fun args _ =>
    (instr_pre 0x101d0 (
      reg_col zesu_sys_regs ∗
      "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
      "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (zkvmExitCode args)) ∗
      0x2401a0d0 ↦ₘ (Z_to_bv 64 (zkvmExitCode args)) ∗
      True))%I
|}.

Lemma zkvm_exit_islaris_contract `{!islaG Σ} `{!threadG} :
  instr 0x101c4 (Some a101c4) -∗
  instr 0x101c8 (Some a101c8) -∗
  instr 0x101cc (Some a101cc) -∗
  IslarisContractSpec 0x101c4 zkvm_exit_contract_resources.
Proof.
  iStartProof.
  unfold IslarisContractSpec.
  iIntros "H101c4 H101c8 H101cc" (args) "Hentry".
  destruct args as [code].
  iDestruct "Hentry" as (old_x5 old_exit_code)
    "(%Hcode & Hregs & Hx5 & Hx10 & HexitCode)".
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: liShow.
  all: try bv_solve.
Qed.
