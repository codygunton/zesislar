From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisMachine.

Lemma zesu_register_aliases_use_one_definition :
  zesu_ram_sys_regs = zesu_instr_sys_regs.
Proof. reflexivity. Qed.

Lemma zesu_ld_uses_the_zesu_machine `{!islaG Sigma} `{!threadG}
    pc destination base offset :
  @zesu_ld_spec Sigma _ _ pc destination base offset =
  @rv64_ld_spec Sigma _ _ zesu_sys_regs 0x20000000 0x40000000
    pc destination base offset.
Proof. reflexivity. Qed.

Lemma zesu_sd_uses_the_zesu_machine `{!islaG Sigma} `{!threadG}
    pc source base offset :
  @zesu_sd_spec Sigma _ _ pc source base offset =
  @rv64_sd_spec Sigma _ _ zesu_sys_regs 0x20000000 0x40000000
    pc source base offset.
Proof. reflexivity. Qed.
