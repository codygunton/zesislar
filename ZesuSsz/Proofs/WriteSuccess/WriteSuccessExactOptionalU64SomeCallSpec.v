Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomePrefix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeJumpHandoff.

Import ZesuSsz.Automation.Calls.FramedContinuations.

Definition optionalU64SomeExactCallEntry `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x5 old_x6 old_x8 old_x11 : bv 64)
    (tag : bv 8) (bytes : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits old_x8 ∗ "x10" ↦ᵣ RVal_Bits pointer ∗
   "x11" ↦ᵣ RVal_Bits old_x11 ∗ bv_unsigned pointer ↦ₘ∗ bytes ∗
   (bv_unsigned sp - 32) ↦ₘ? 32 ∗
   ⌜bytes !! 8%nat = Some tag⌝ ∗ ⌜tag <> BV 8 0⌝ ∗
   ⌜value = Z_to_bv 64 (little_endian_to_bv 8 (take 8 bytes))⌝ ∗
   ⌜(8 <= length bytes)%nat⌝ ∗ ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗
   ⌜bv_unsigned pointer + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   optionalU64SomeExactCallContext pointer value sp ret old_x5 old_x6 old_x8
     bytes tail P ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64SomeExactCallEntry) := I.

Lemma optional_u64_some_exact_call_entry `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x5 old_x6 old_x8 old_x11 : bv 64)
    (tag : bv 8) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_body 0x15bc8 (optionalU64SomeExactEntry pointer value sp ret old_x8
    old_x11 tag bytes (optionalU64SomeExactCallContext pointer value sp ret
      old_x5 old_x6 old_x8 bytes tail P)) -∗
  instr_body 0x15be8 (optionalU64SomeExactPrefixPost pointer value sp ret old_x8
    (bv_zero_extend 64 tag) bytes (optionalU64SomeExactCallContext pointer value
      sp ret old_x5 old_x6 old_x8 bytes tail P)) -∗
  instr_body 0x15bc8 (optionalU64SomeExactCallEntry pointer value sp ret old_x5
    old_x6 old_x8 old_x11 tag bytes tail P).
Proof.
  iStartProof. iIntros "Hbranch Hjump".
  iApply (instr_pre_wand 0x15bc8 0x15bc8 false false with "Hbranch");
    [done | done |].
  iIntros "Hentry". iDestruct "Hentry" as
    "(Hsys & H1 & H2 & H8 & H10 & H11 & Hsource & Hstack & %Htag & %Hnonzero &
      %Hvalue & %Hlength & %Hpointer & %Hlower & %Hupper & %Hsp4 & %Hmin & %Hmax &
      Hcontext & _)".
  iDestruct "Hcontext" as
    "(H5 & H6 & Hmmio & Htrace & %HcontextSp4 & %Halign & %HcontextMin &
      %HcontextMax & %Hret0 & %Hret1 & %Hret2 & HP & Hnext & _)".
  zesu_run.
Qed.

Print Assumptions optional_u64_some_exact_call_entry.
