Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneEntry.

Import ZesuSsz.Automation.Calls.FramedContinuations.

Definition optionalU64NoneExactUnusedStack `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp - 32) ↦ₘ? 16 ∗ P ∗ True)%I.

Definition optionalU64NoneExactCallPost `{!islaG Sigma} `{!threadG}
    (pointer sp ret : bv 64) (bytes : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x6" ↦ᵣ RVal_Bits (BV 64 0x15c08) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 9)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
   (bv_unsigned sp - 32) ↦ₘ? 32 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ optionalU64NoneObjectFrame pointer bytes P ∗ True)%I.

Definition optionalU64NoneExactCallEntry `{!islaG Sigma} `{!threadG}
    (pointer sp ret old_x5 old_x6 old_x11 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
   "x10" ↦ᵣ RVal_Bits pointer ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
   (bv_unsigned sp - 32) ↦ₘ? 32 ∗ bv_unsigned pointer ↦ₘ∗ bytes ∗
   ⌜bytes !! 8%nat = Some (BV 8 0)⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗
   ⌜bv_unsigned pointer + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
     (writeSuccessBooleanWordPayload (BV 64 0)) tail) ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗ instr_pre (bv_unsigned ret)
     (optionalU64NoneExactCallPost pointer sp ret bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64NoneExactUnusedStack) := I.
Global Instance : LithiumUnfold (@optionalU64NoneExactCallPost) := I.
Global Instance : LithiumUnfold (@optionalU64NoneExactCallEntry) := I.

Lemma optional_u64_none_exact_call_entry `{!islaG Sigma} `{!threadG}
    (pointer sp ret old_x5 old_x6 old_x11 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_body 0x15bc8 (optionalU64NoneExactEntry pointer sp ret old_x5 old_x6
    old_x11 bytes tail (optionalU64NoneExactUnusedStack sp P)) -∗
  instr_body 0x15bc8 (optionalU64NoneExactCallEntry pointer sp ret old_x5 old_x6
    old_x11 bytes tail P).
Proof.
  iStartProof. iIntros "Hbody".
  iApply (instr_pre_wand 0x15bc8 0x15bc8 false false with "Hbody");
    [done | done |].
  iIntros "Hentry". iDestruct "Hentry" as
    "(Hsys & H1 & H2 & H5 & H6 & H10 & H11 & Hstack & Hsource & %Htag &
      %Hlower & %Hupper & Hmmio & Htrace & %Hsp4 & %Hsp3 & %Hmin & %Hmax &
      %Hret0 & %Hret1 & %Hret2 & HP & Hnext & _)".
  zesu_run.
Qed.

Print Assumptions optional_u64_none_exact_call_entry.
