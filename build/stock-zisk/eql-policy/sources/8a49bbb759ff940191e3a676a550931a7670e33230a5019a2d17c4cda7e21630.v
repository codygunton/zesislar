Require Import ZesuSsz.Automation.All.
From Coq Require Import Strings.String Lists.List ZArith.ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.PlatformLoadRegion.
Open Scope string_scope.
Open Scope Z_scope.

Definition heldoutSignatureEntry `{!islaG Sigma} `{!threadG}
  (returnAddress : Z)
  (stackCapacity : Z)
  (leftWord : bv 64%N)
  (rightWord : bv 64%N)
  (stackWord : bv 64%N)
  (returnWord : bv 64%N)
  (leftBytes : list (bv 8%N))
  (rightBytes : list (bv 8%N))
  (leftFraction : Qp)
  (rightFraction : Qp)
  (K : iProp Sigma)
  (saved_x8 : bv 64%N)
  (saved_x9 : bv 64%N)
  (saved_x18 : bv 64%N)
  (saved_x19 : bv 64%N)
  (saved_x20 : bv 64%N)
  (saved_x21 : bv 64%N)
  (saved_x22 : bv 64%N)
  (saved_x23 : bv 64%N)
  (saved_x24 : bv 64%N)
  (saved_x25 : bv 64%N)
  (saved_x26 : bv 64%N)
  (saved_x27 : bv 64%N) : iProp Sigma :=
  (∃ (actualInputEnd : bv 64%N)
      (leftLoadRegion : platformLoadRegion defaultMap actualInputEnd leftWord 20%Z)
      (rightLoadRegion : platformLoadRegion defaultMap actualInputEnd rightWord 20%Z)
      (temporary_x5 : bv 64%N) (temporary_x6 : bv 64%N) (temporary_x7 : bv 64%N) (temporary_x12 : bv 64%N) (temporary_x13 : bv 64%N) (temporary_x14 : bv 64%N) (temporary_x15 : bv 64%N) (temporary_x16 : bv 64%N) (temporary_x17 : bv 64%N) (temporary_x28 : bv 64%N) (temporary_x29 : bv 64%N) (temporary_x30 : bv 64%N) (temporary_x31 : bv 64%N),
  reg_col (platformResidualSystemRegs defaultMap) ∗
  "zisk_input_end" ↦ᵣ RVal_Bits actualInputEnd ∗
  "x5" ↦ᵣ RVal_Bits temporary_x5 ∗
  "x6" ↦ᵣ RVal_Bits temporary_x6 ∗
  "x7" ↦ᵣ RVal_Bits temporary_x7 ∗
  "x12" ↦ᵣ RVal_Bits temporary_x12 ∗
  "x13" ↦ᵣ RVal_Bits temporary_x13 ∗
  "x14" ↦ᵣ RVal_Bits temporary_x14 ∗
  "x15" ↦ᵣ RVal_Bits temporary_x15 ∗
  "x16" ↦ᵣ RVal_Bits temporary_x16 ∗
  "x17" ↦ᵣ RVal_Bits temporary_x17 ∗
  "x28" ↦ᵣ RVal_Bits temporary_x28 ∗
  "x29" ↦ᵣ RVal_Bits temporary_x29 ∗
  "x30" ↦ᵣ RVal_Bits temporary_x30 ∗
  "x31" ↦ᵣ RVal_Bits temporary_x31 ∗
  "x8" ↦ᵣ RVal_Bits saved_x8 ∗
  "x9" ↦ᵣ RVal_Bits saved_x9 ∗
  "x18" ↦ᵣ RVal_Bits saved_x18 ∗
  "x19" ↦ᵣ RVal_Bits saved_x19 ∗
  "x20" ↦ᵣ RVal_Bits saved_x20 ∗
  "x21" ↦ᵣ RVal_Bits saved_x21 ∗
  "x22" ↦ᵣ RVal_Bits saved_x22 ∗
  "x23" ↦ᵣ RVal_Bits saved_x23 ∗
  "x24" ↦ᵣ RVal_Bits saved_x24 ∗
  "x25" ↦ᵣ RVal_Bits saved_x25 ∗
  "x26" ↦ᵣ RVal_Bits saved_x26 ∗
  "x27" ↦ᵣ RVal_Bits saved_x27 ∗
  "x1" ↦ᵣ RVal_Bits returnWord ∗
  "x2" ↦ᵣ RVal_Bits stackWord ∗
  "x10" ↦ᵣ RVal_Bits leftWord ∗
  "x11" ↦ᵣ RVal_Bits rightWord ∗
  (bv_unsigned leftWord) ↦ₘ{DfracOwn leftFraction}∗ leftBytes ∗
  (bv_unsigned rightWord) ↦ₘ{DfracOwn rightFraction}∗ rightBytes ∗
  (bv_unsigned stackWord - stackCapacity) ↦ₘ? stackCapacity ∗
  K ∗
  ⌜(List.length leftBytes = 20)%nat⌝ ∗
  ⌜(List.length rightBytes = 20)%nat⌝ ∗
  ⌜(bv_unsigned leftWord + 20 <= 2^64)%Z⌝ ∗
  ⌜(bv_unsigned rightWord + 20 <= 2^64)%Z⌝ ∗
  ⌜(0 <= stackCapacity)%Z⌝ ∗
  ⌜(16 <= stackCapacity)%Z⌝ ∗
  ⌜(mapRamBase defaultMap <= bv_unsigned stackWord - stackCapacity)%Z⌝ ∗
  ⌜(bv_unsigned stackWord < machineRamEnd defaultMap)%Z⌝ ∗
  ⌜(bv_unsigned stackWord mod 16 = 0)%Z⌝ ∗
  ⌜(bv_unsigned returnWord = returnAddress)%Z⌝ ∗
  ⌜(bv_unsigned returnWord mod 4 = 0)%Z⌝ ∗
  True)%I.
