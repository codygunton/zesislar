From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a15694.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlocker.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessBlockerSp : bv 64 := BV 64 0x20001000.
Definition writeSuccessBlockerPointer : bv 64 := BV 64 0x20001000.
Definition writeSuccessBlockerScratchBefore : list (bv 8) :=
  repeat (Z_to_bv 8 0) 48.
Definition writeSuccessBlockerEncoderScratch : list (bv 8) :=
  repeat (Z_to_bv 8 0) 16.

Lemma writeSuccessBlockerSpUnsigned :
  bv_unsigned writeSuccessBlockerSp = 0x20001000.
Proof. vm_compute. reflexivity. Qed.

Lemma writeSuccessBlockerScratchAddress :
  bv_unsigned writeSuccessBlockerSp + 1744 = writeSuccessBlockerScratch.
Proof. rewrite writeSuccessBlockerSpUnsigned. reflexivity. Qed.

Definition writeSuccessBlockerArgs : WriteSuccessArgs WriteSuccessObservation := {|
  successReturnAddress := 0;
  successStackPointer := 0x200017d0;
  successDecodedAddress := writeSuccessBlockerOwner;
  successDecoded := writeSuccessBlockerDecoded;
  successInputSize := 0
|}.

Definition writeSuccessBlockerRegs : reg_map :=
  <["PC" := RVal_Bits (BV 64 0x15694)]> $
  <["x1" := RVal_Bits (BV 64 0)]> $
  <["x2" := RVal_Bits writeSuccessBlockerSp]> $
  <["x3" := RVal_Bits (BV 64 0)]> $
  <["x4" := RVal_Bits (BV 64 0)]> $
  <["x5" := RVal_Bits (BV 64 0)]> $
  <["x6" := RVal_Bits (BV 64 0)]> $
  <["x7" := RVal_Bits (BV 64 0)]> $
  <["x8" := RVal_Bits writeSuccessBlockerPointer]> $
  <["x9" := RVal_Bits (Z_to_bv 64 2)]> $
  <["x10" := RVal_Bits (BV 64 0)]> $
  <["x11" := RVal_Bits (BV 64 0)]> $
  <["x12" := RVal_Bits (BV 64 0)]> $
  <["x13" := RVal_Bits (BV 64 0)]> $
  <["x14" := RVal_Bits (BV 64 0)]> $
  <["x15" := RVal_Bits (BV 64 0)]> $
  <["x16" := RVal_Bits (BV 64 0)]> $
  <["x17" := RVal_Bits (BV 64 0)]> $
  <["x18" := RVal_Bits (writeSuccessBlockerSp + BV 64 1768)%bv]> $
  <["x19" := RVal_Bits (BV 64 0)]> $
  <["x20" := RVal_Bits (BV 64 0)]> $
  <["x21" := RVal_Bits (BV 64 0)]> $
  <["x22" := RVal_Bits (BV 64 0)]> $
  <["x23" := RVal_Bits (BV 64 0)]> $
  <["x24" := RVal_Bits (BV 64 0)]> $
  <["x25" := RVal_Bits (BV 64 0)]> $
  <["x26" := RVal_Bits (BV 64 0)]> $
  <["x27" := RVal_Bits (BV 64 0)]> $
  <["x28" := RVal_Bits (BV 64 0)]> $
  <["x29" := RVal_Bits (BV 64 0)]> $
  <["x30" := RVal_Bits (BV 64 0)]> $
  <["x31" := RVal_Bits (BV 64 0)]> $
  <["rv_enable_pmp" := RVal_Bool false]> $
  <["rv_enable_misaligned_access" := RVal_Bool false]> $
  <["rv_ram_base" := RVal_Bits (BV 64 0x20000000)]> $
  <["rv_ram_size" := RVal_Bits (BV 64 0x20000000)]> $
  <["rv_rom_base" := RVal_Bits (BV 64 0x1000)]> $
  <["rv_rom_size" := RVal_Bits (BV 64 0x100)]> $
  <["rv_clint_base" := RVal_Bits (BV 64 0x2000000)]> $
  <["rv_clint_size" := RVal_Bits (BV 64 0xc0000)]> $
  <["rv_htif_tohost" := RVal_Bits (BV 64 0x40001000)]> $
  <["cur_privilege" := RVal_Enum "Machine"]> $
  <["misa" := RegVal_Struct
      [("bits", RVal_Bits (BV 64 0x8000000000001100))]]> $
  <["mtvec" := RegVal_Struct [("bits", RVal_Bits (BV 64 0))]]> $
  <["mstatus" := RegVal_Struct [("bits", RVal_Bits (BV 64 0))]]> $
  <["satp" := RVal_Bits (BV 64 0)]> (∅ : reg_map).

Definition writeSuccessBlockerInstrs : gmap addr isla_trace :=
  list_to_map (map (fun item => (Z_to_bv 64 item.1, item.2))
    writeSuccessWithdrawalsInstructionMap).

Definition writeSuccessBlockerGlobal : seq_global_state := {|
  seq_instrs := writeSuccessBlockerInstrs;
  seq_mem := writeSuccessBlockerRepresentedMemory
|}.

Definition writeSuccessBlockerLocal : seq_local_state := {|
  seq_trace := IslaTraces.write_success_90.a15694.a15694;
  seq_regs := writeSuccessBlockerRegs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccessBlockerState : WriteSuccessWithdrawalsConcreteState :=
  ((writeSuccessBlockerLocal, writeSuccessBlockerGlobal), []).

Lemma writeSuccessBlockerLocalFields :
  writeSuccessBlockerLocal.(seq_pc_reg) = "PC" /\
  writeSuccessBlockerLocal.(seq_nb_state) = false /\
  writeSuccessBlockerLocal.(seq_regs) = writeSuccessBlockerRegs.
Proof. repeat split; reflexivity. Qed.

Lemma writeSuccessBlockerLocalPcReg :
  writeSuccessBlockerLocal.(seq_pc_reg) = "PC".
Proof. reflexivity. Qed.

Lemma writeSuccessBlockerLocalRegs :
  writeSuccessBlockerLocal.(seq_regs) = writeSuccessBlockerRegs.
Proof. reflexivity. Qed.

Lemma writeSuccessBlockerGlobalMemory :
  writeSuccessBlockerGlobal.(seq_mem) = writeSuccessBlockerRepresentedMemory.
Proof. reflexivity. Qed.

Lemma writeSuccessBlockerConcretePc :
  writeSuccessWithdrawalsConcretePc writeSuccessBlockerState = Some 0x15694.
Proof.
  unfold writeSuccessWithdrawalsConcretePc, writeSuccessBlockerState.
  cbn. native_compute; reflexivity.
Qed.

Lemma writeSuccessBlockerEntryRegisterLookups :
  (exists oldX1, writeSuccessBlockerRegs !! "x1" = Some oldX1) /\
  writeSuccessBlockerRegs !! "x2" = Some (RVal_Bits writeSuccessBlockerSp) /\
  (exists oldX10, writeSuccessBlockerRegs !! "x10" = Some oldX10) /\
  (exists oldX11, writeSuccessBlockerRegs !! "x11" = Some oldX11) /\
  (exists oldX12, writeSuccessBlockerRegs !! "x12" = Some oldX12) /\
  (exists oldX15, writeSuccessBlockerRegs !! "x15" = Some oldX15) /\
  writeSuccessBlockerRegs !! "x8" =
    Some (RVal_Bits writeSuccessBlockerPointer) /\
  writeSuccessBlockerRegs !! "x9" = Some (RVal_Bits (Z_to_bv 64 2)) /\
  writeSuccessBlockerRegs !! "x18" =
    Some (RVal_Bits (writeSuccessBlockerSp + BV 64 1768)%bv).
Proof. repeat split; try eexists; native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerRegisterFacts :
  writeSuccessWithdrawalsOperationalRegisterFacts writeSuccessBlockerRegs.
Proof.
  unfold writeSuccessWithdrawalsOperationalRegisterFacts,
    writeSuccessWithdrawalsOperationalMstatus.
  split; [native_compute; reflexivity|].
  split.
  - unfold zesu_ram_sys_regs, zesu_sys_regs,
      writeSuccessWithdrawalsOperationalRegisterShape.
    cbn. repeat constructor; eexists; repeat split;
      native_compute; reflexivity.
  - intros register Hregister. cbn in Hregister.
    repeat destruct Hregister as [Hregister|Hregister];
      try (subst register; eexists; native_compute; reflexivity).
    contradiction.
Qed.

Lemma writeSuccessBlockerRegisterFrame :
  writeSuccessWithdrawalsRegisterFrame writeSuccessBlockerRegs
    writeSuccessBlockerRegs.
Proof.
  unfold writeSuccessWithdrawalsRegisterFrame,
    writeSuccessWithdrawalsProtectedRegisters.
  repeat constructor; reflexivity.
Qed.

Lemma writeSuccessBlockerMemoryFrame :
  writeSuccessWithdrawalsMemoryFrame writeSuccessBlockerSp
    writeSuccessBlockerRepresentedMemory writeSuccessBlockerRepresentedMemory.
Proof. split; [reflexivity|intros; reflexivity]. Qed.

Print Assumptions writeSuccessBlockerRegisterFacts.
Print Assumptions writeSuccessBlockerEntryRegisterLookups.
Print Assumptions writeSuccessBlockerRegisterFrame.
Print Assumptions writeSuccessBlockerMemoryFrame.
