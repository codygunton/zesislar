Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Open Scope Z_scope.

Definition machineEntry6960 `{!islaG Sigma} `{!threadG}
  (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) (entry_fact_0 : (decodeItemReturnAddress ( args ) = ( returnAddress ))%Z) (entry_fact_1 : (( decodeItemInputLength ( args ) ) = Z.of_nat ( List.length ( decodeItemInputBytes ( args ) ) ))%Z) (entry_fact_2 : (List.length ( decodeItemBeforeStorage ( args ) ) = 40)%nat) (entry_fact_3 : (0 <= ( decodeItemInputPointer ( args ) ))%Z) (entry_fact_4 : (0 <= ( decodeItemInputLength ( args ) ))%Z) (entry_fact_5 : (0 <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_6 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_7 : (( decodeItemOutputPointer ( args ) ) + 40 < ( 18446744073709551616 ))%Z) (entry_fact_8 : (( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_9 : (( decodeItemStackPointer ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_10 : (( 2684354560 ) + ( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_11 : (( decodeItemStackPointer ( args ) ) <= ( 3221225472 ))%Z) (entry_fact_12 : (0 <= ( decodeItemReturnAddress ( args ) ))%Z) (entry_fact_13 : (( decodeItemReturnAddress ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_14 : (( decodeItemReturnAddress ( args ) ) mod 4 = 0)%Z) (entry_fact_15 : (( 2684354560 ) <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_16 : (( decodeItemOutputPointer ( args ) ) + 40 <= ( 3221225472 ))%Z) (entry_fact_17 : (0 <= ( decodeItemInputEnd ( args ) ))%Z) (entry_fact_18 : (( decodeItemInputEnd ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_19 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) <= ( decodeItemInputEnd ( args ) ))%Z) : iProp Sigma :=
  (∃ (a3 : bv 64%N) (a4 : bv 64%N) (a5 : bv 64%N) (a6 : bv 64%N) (machine_x12 : bv 64%N) (machine_x2 : bv 64%N),
  reg_col ((decodeItemSysRegs args)) ∗
  "x10" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemOutputPointer args))) : bv 64%N)) ∗
  "x11" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemInputPointer args))) : bv 64%N)) ∗
  "x12" ↦ᵣ (RVal_Bits (machine_x12 : bv 64)) ∗
  "x13" ↦ᵣ (RVal_Bits (a3 : bv 64%N)) ∗
  "x14" ↦ᵣ (RVal_Bits (a4 : bv 64%N)) ∗
  "x15" ↦ᵣ (RVal_Bits (a5 : bv 64%N)) ∗
  "x16" ↦ᵣ (RVal_Bits (a6 : bv 64%N)) ∗
  "x2" ↦ᵣ (RVal_Bits (machine_x2 : bv 64)) ∗
  "x1" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemReturnAddress args))) : bv 64%N)) ∗
  "x8" ↦ᵣ (RVal_Bits ((decodeItemSavedFramePointer args) : bv 64%N)) ∗
  (decodeItemInputPointer args) ↦ₘ∗ (decodeItemInputBytes args) ∗
  (decodeItemOutputPointer args) ↦ₘ∗ (decodeItemBeforeStorage args) ∗
  (decodeItemStackPointer args - ( 16 )) ↦ₘ? (16) ∗
  K ∗
  ⌜(bv_unsigned machine_x12 = (decodeItemInputLength args))%Z⌝ ∗
  ⌜(bv_unsigned machine_x2 = (decodeItemStackPointer args))%Z⌝ ∗
  True)%I.

Definition machineAt6974 `{!islaG Sigma} `{!threadG}
  (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) (entry_fact_0 : (decodeItemReturnAddress ( args ) = ( returnAddress ))%Z) (entry_fact_1 : (( decodeItemInputLength ( args ) ) = Z.of_nat ( List.length ( decodeItemInputBytes ( args ) ) ))%Z) (entry_fact_2 : (List.length ( decodeItemBeforeStorage ( args ) ) = 40)%nat) (entry_fact_3 : (0 <= ( decodeItemInputPointer ( args ) ))%Z) (entry_fact_4 : (0 <= ( decodeItemInputLength ( args ) ))%Z) (entry_fact_5 : (0 <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_6 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_7 : (( decodeItemOutputPointer ( args ) ) + 40 < ( 18446744073709551616 ))%Z) (entry_fact_8 : (( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_9 : (( decodeItemStackPointer ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_10 : (( 2684354560 ) + ( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_11 : (( decodeItemStackPointer ( args ) ) <= ( 3221225472 ))%Z) (entry_fact_12 : (0 <= ( decodeItemReturnAddress ( args ) ))%Z) (entry_fact_13 : (( decodeItemReturnAddress ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_14 : (( decodeItemReturnAddress ( args ) ) mod 4 = 0)%Z) (entry_fact_15 : (( 2684354560 ) <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_16 : (( decodeItemOutputPointer ( args ) ) + 40 <= ( 3221225472 ))%Z) (entry_fact_17 : (0 <= ( decodeItemInputEnd ( args ) ))%Z) (entry_fact_18 : (( decodeItemInputEnd ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_19 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) <= ( decodeItemInputEnd ( args ) ))%Z) : iProp Sigma :=
  (∃ (a3 : bv 64%N) (a4 : bv 64%N) (a5 : bv 64%N) (a6 : bv 64%N) (machine_x12 : bv 64%N) (machine_x2 : bv 64%N) (machine_x8 : bv 64%N) (machine_input_byte : bv 8%N),
  reg_col ((decodeItemSysRegs args)) ∗
  "x10" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemOutputPointer args))) : bv 64%N)) ∗
  "x11" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemInputPointer args))) : bv 64%N)) ∗
  "x12" ↦ᵣ (RVal_Bits (machine_x12 : bv 64)) ∗
  "x13" ↦ᵣ (RVal_Bits (a3 : bv 64%N)) ∗
  "x14" ↦ᵣ (RVal_Bits (a4 : bv 64%N)) ∗
  "x15" ↦ᵣ (RVal_Bits (a5 : bv 64%N)) ∗
  "x16" ↦ᵣ (RVal_Bits (a6 : bv 64%N)) ∗
  "x2" ↦ᵣ (RVal_Bits (machine_x2 : bv 64)) ∗
  "x1" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemReturnAddress args))) : bv 64%N)) ∗
  "x8" ↦ᵣ (RVal_Bits (machine_x8 : bv 64)) ∗
  (decodeItemInputPointer args) ↦ₘ{DfracOwn 1}∗ (decodeItemInputBytes args) ∗
  (decodeItemOutputPointer args) ↦ₘ{DfracOwn 1}∗ (decodeItemBeforeStorage args) ∗
  (decodeItemStackPointer args - ( 16 )) ↦ₘ{DfracOwn 1}∗ (((Coq.Init.Datatypes.cons ((bv_extract 0%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 8%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 16%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 24%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 32%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 40%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 48%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 56%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 0%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 8%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 16%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 24%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 32%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 40%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 48%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 56%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (@Coq.Init.Datatypes.nil (bv 8%N)))))))))))))))))))) ∗
  K ∗
  ⌜(bv_unsigned machine_x12 = (decodeItemInputLength args))%Z⌝ ∗
  ⌜(bv_unsigned machine_x2 = ((decodeItemStackPointer args) + (-16)))%Z⌝ ∗
  ⌜(bv_unsigned machine_x8 = (((decodeItemStackPointer args) + (-16)) + (16)))%Z⌝ ∗
  ⌜(0 < bv_unsigned machine_x12)%Z⌝ ∗
  ⌜(( ( ( ((bv_unsigned machine_x2) - (-16)) ) + ( - 16 ) ) + ( 8 ) ) >= ( 2684354560 ))%Z⌝ ∗
  ⌜(( ( ( ( ((bv_unsigned machine_x2) - (-16)) ) + ( - 16 ) ) + ( 8 ) ) + ( 8 ) ) <= ( 3221225472 ))%Z⌝ ∗
  ⌜(( ( ((bv_unsigned machine_x2) - (-16)) ) + ( - 16 ) ) >= ( 2684354560 ))%Z⌝ ∗
  ⌜(( ( ( ((bv_unsigned machine_x2) - (-16)) ) + ( - 16 ) ) + ( 8 ) ) <= ( 3221225472 ))%Z⌝ ∗
  ⌜List.nth_error (decodeItemInputBytes ( args )) 0%nat = Some machine_input_byte⌝ ∗
  ⌜((0 <= bv_unsigned machine_input_byte <= 255)%Z)%Z⌝ ∗
  ⌜(bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)) = (decodeItemInputPointer args))%Z⌝ ∗
  True)%I.

Definition machineAt6ae0 `{!islaG Sigma} `{!threadG}
  (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) (entry_fact_0 : (decodeItemReturnAddress ( args ) = ( returnAddress ))%Z) (entry_fact_1 : (( decodeItemInputLength ( args ) ) = Z.of_nat ( List.length ( decodeItemInputBytes ( args ) ) ))%Z) (entry_fact_2 : (List.length ( decodeItemBeforeStorage ( args ) ) = 40)%nat) (entry_fact_3 : (0 <= ( decodeItemInputPointer ( args ) ))%Z) (entry_fact_4 : (0 <= ( decodeItemInputLength ( args ) ))%Z) (entry_fact_5 : (0 <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_6 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_7 : (( decodeItemOutputPointer ( args ) ) + 40 < ( 18446744073709551616 ))%Z) (entry_fact_8 : (( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_9 : (( decodeItemStackPointer ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_10 : (( 2684354560 ) + ( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_11 : (( decodeItemStackPointer ( args ) ) <= ( 3221225472 ))%Z) (entry_fact_12 : (0 <= ( decodeItemReturnAddress ( args ) ))%Z) (entry_fact_13 : (( decodeItemReturnAddress ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_14 : (( decodeItemReturnAddress ( args ) ) mod 4 = 0)%Z) (entry_fact_15 : (( 2684354560 ) <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_16 : (( decodeItemOutputPointer ( args ) ) + 40 <= ( 3221225472 ))%Z) (entry_fact_17 : (0 <= ( decodeItemInputEnd ( args ) ))%Z) (entry_fact_18 : (( decodeItemInputEnd ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_19 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) <= ( decodeItemInputEnd ( args ) ))%Z) : iProp Sigma :=
  (∃ (a3 : bv 64%N) (a4 : bv 64%N) (a5 : bv 64%N) (a6 : bv 64%N) (machine_x12 : bv 64%N) (machine_x2 : bv 64%N) (machine_x8 : bv 64%N),
  reg_col ((decodeItemSysRegs args)) ∗
  "x10" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemOutputPointer args))) : bv 64%N)) ∗
  "x11" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemInputPointer args))) : bv 64%N)) ∗
  "x12" ↦ᵣ (RVal_Bits (machine_x12 : bv 64)) ∗
  "x13" ↦ᵣ (RVal_Bits (a3 : bv 64%N)) ∗
  "x14" ↦ᵣ (RVal_Bits (a4 : bv 64%N)) ∗
  "x15" ↦ᵣ (RVal_Bits (a5 : bv 64%N)) ∗
  "x16" ↦ᵣ (RVal_Bits (a6 : bv 64%N)) ∗
  "x2" ↦ᵣ (RVal_Bits (machine_x2 : bv 64)) ∗
  "x1" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemReturnAddress args))) : bv 64%N)) ∗
  "x8" ↦ᵣ (RVal_Bits (machine_x8 : bv 64)) ∗
  (decodeItemInputPointer args) ↦ₘ{DfracOwn 1}∗ (decodeItemInputBytes args) ∗
  (decodeItemOutputPointer args) ↦ₘ{DfracOwn 1}∗ (decodeItemBeforeStorage args) ∗
  (decodeItemStackPointer args - ( 16 )) ↦ₘ{DfracOwn 1}∗ (((Coq.Init.Datatypes.cons ((bv_extract 0%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 8%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 16%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 24%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 32%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 40%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 48%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 56%N 8%N (decodeItemSavedFramePointer args)) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 0%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 8%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 16%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 24%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 32%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 40%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 48%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (Coq.Init.Datatypes.cons ((bv_extract 56%N 8%N ((Z_to_bv 64%N (decodeItemReturnAddress args)))) : bv 8%N) (@Coq.Init.Datatypes.nil (bv 8%N)))))))))))))))))))) ∗
  K ∗
  ⌜(bv_unsigned machine_x12 = (decodeItemInputLength args))%Z⌝ ∗
  ⌜(bv_unsigned machine_x2 = ((decodeItemStackPointer args) + (-16)))%Z⌝ ∗
  ⌜(bv_unsigned machine_x8 = (((decodeItemStackPointer args) + (-16)) + (16)))%Z⌝ ∗
  ⌜(bv_unsigned machine_x12 = 0)%Z⌝ ∗
  ⌜(( ( ( ((bv_unsigned machine_x2) - (-16)) ) + ( - 16 ) ) + ( 8 ) ) >= ( 2684354560 ))%Z⌝ ∗
  ⌜(( ( ( ( ((bv_unsigned machine_x2) - (-16)) ) + ( - 16 ) ) + ( 8 ) ) + ( 8 ) ) <= ( 3221225472 ))%Z⌝ ∗
  ⌜(( ( ((bv_unsigned machine_x2) - (-16)) ) + ( - 16 ) ) >= ( 2684354560 ))%Z⌝ ∗
  ⌜(( ( ( ((bv_unsigned machine_x2) - (-16)) ) + ( - 16 ) ) + ( 8 ) ) <= ( 3221225472 ))%Z⌝ ∗
  True)%I.
