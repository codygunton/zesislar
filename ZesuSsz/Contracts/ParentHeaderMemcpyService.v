From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ZiskRuntime.

Open Scope Z_scope.

Definition memcpyCsrPc : Z := 0x800e06c0.
Definition parentHeaderMemcpySource : Z := 0x80114fb8.
Definition parentHeaderMemcpyLength : Z := 80.

Definition parentHeaderMemcpyArguments (destination returnAddress : Z) :
    ZiskMemcpyArguments :=
  {| ziskMemcpyDestination := destination;
     ziskMemcpySource := parentHeaderMemcpySource;
     ziskMemcpyLength := parentHeaderMemcpyLength;
     ziskMemcpyReturnAddress := returnAddress |}.

Definition ziskRuntimeBytesAt (state : ZiskRuntimeState unit)
    (address : Z) (count : nat) : list byte :=
  List.map (fun offset => Z_to_bv 8
    (ziskRuntimeMemory state (address + Z.of_nat offset)))
    (List.seq 0 count).

(* This premise covers only the reached 80-byte copy. The three array
   resources exclude overlap. The generic overlapping memcpy contract
   in ZiskRuntime.v is outside this Islaris premise. *)
Definition ziskMemcpyServiceEntry `{!islaG Sigma} `{!threadG}
    (permissions : ZiskRuntimePermissions) (destination returnAddress : Z)
    (before : ZiskRuntimeState unit) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 destination) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 parentHeaderMemcpySource) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 parentHeaderMemcpyLength) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 returnAddress) ∗
   parentHeaderMemcpySource ↦ₘ∗
     ziskRuntimeBytesAt before parentHeaderMemcpySource 80 ∗
   destination ↦ₘ∗ ziskRuntimeBytesAt before destination 80 ∗
   ziskExtraParamsAddress ↦ₘ∗
     ziskRuntimeBytesAt before ziskExtraParamsAddress 8 ∗
   ⌜ziskMemcpyEntry permissions memcpyCsrPc
      (parentHeaderMemcpyArguments destination returnAddress) before⌝ ∗
   True)%I.

Definition ziskMemcpyServiceExit `{!islaG Sigma} `{!threadG}
    (destination returnAddress : Z) (after : ZiskRuntimeState unit) :
    iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 destination) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 parentHeaderMemcpySource) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 parentHeaderMemcpyLength) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 returnAddress) ∗
   parentHeaderMemcpySource ↦ₘ∗
     ziskRuntimeBytesAt after parentHeaderMemcpySource 80 ∗
   destination ↦ₘ∗ ziskRuntimeBytesAt after destination 80 ∗
   ziskExtraParamsAddress ↦ₘ∗
     ziskRuntimeBytesAt after ziskExtraParamsAddress 8 ∗
   True)%I.

Definition ziskMemcpyServiceInstrSpec `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (∀ (permissions : ZiskRuntimePermissions) (destination returnAddress : Z)
     (before : ZiskRuntimeState unit),
     ziskMemcpyServiceEntry permissions destination returnAddress before -∗
     instr_pre (Z.land returnAddress (-2))
       (∃ after : ZiskRuntimeState unit,
          ⌜ziskMemcpyAllows selectedMemcpy permissions
             (parentHeaderMemcpyArguments destination returnAddress)
             before after⌝ ∗
          ziskMemcpyServiceExit destination returnAddress after))%I.

Definition memcpyServicePremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre memcpyCsrPc ziskMemcpyServiceInstrSpec)%I.
