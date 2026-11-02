Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.MachinePilot322LoweredEntries.
Require Import ZesuSsz.Generated.DecodeItem.MachinePilot322LoweredStructural.
Require Import ZesuSsz.Generated.DecodeItem.MachinePilot323Entries.
Require Import ZesuSsz.Generated.DecodeItem.MachinePilot323Structural.
Require Import ZesuSsz.Generated.DecodeItem.PilotRejectJoin200.
Require Import ZesuSsz.Automation.EffectiveOverrides.
Open Scope Z_scope.

Lemma DesignedBoundary_800d6a08 `{!islaG Sigma} `{!threadG}
 (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) (entry_fact_0 : (decodeItemReturnAddress ( args ) = ( returnAddress ))%Z) (entry_fact_1 : (( decodeItemInputLength ( args ) ) = Z.of_nat ( List.length ( decodeItemInputBytes ( args ) ) ))%Z) (entry_fact_2 : (List.length ( decodeItemBeforeStorage ( args ) ) = 40)%nat) (entry_fact_3 : (0 <= ( decodeItemInputPointer ( args ) ))%Z) (entry_fact_4 : (0 <= ( decodeItemInputLength ( args ) ))%Z) (entry_fact_5 : (0 <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_6 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_7 : (( decodeItemOutputPointer ( args ) ) + 40 < ( 18446744073709551616 ))%Z) (entry_fact_8 : (( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_9 : (( decodeItemStackPointer ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_10 : (( 2684354560 ) + ( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_11 : (( decodeItemStackPointer ( args ) ) <= ( 3221225472 ))%Z) (entry_fact_12 : (0 <= ( decodeItemReturnAddress ( args ) ))%Z) (entry_fact_13 : (( decodeItemReturnAddress ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_14 : (( decodeItemReturnAddress ( args ) ) mod 4 = 0)%Z) (entry_fact_15 : (( 2684354560 ) <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_16 : (( decodeItemOutputPointer ( args ) ) + 40 <= ( 3221225472 ))%Z) (entry_fact_17 : (0 <= ( decodeItemInputEnd ( args ) ))%Z) (entry_fact_18 : (( decodeItemInputEnd ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_19 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) <= ( decodeItemInputEnd ( args ) ))%Z) :
 instr_pre 0x800d6ae0 (machineRejectJoin200 (args) (returnAddress) (K) (entry_fact_0) (entry_fact_1) (entry_fact_2) (entry_fact_3) (entry_fact_4) (entry_fact_5) (entry_fact_6) (entry_fact_7) (entry_fact_8) (entry_fact_9) (entry_fact_10) (entry_fact_11) (entry_fact_12) (entry_fact_13) (entry_fact_14) (entry_fact_15) (entry_fact_16) (entry_fact_17) (entry_fact_18) (entry_fact_19)) -∗
 instr_pre 0x800d6a14 (machineAt6a14_323 (args) (returnAddress) (K) (entry_fact_0) (entry_fact_1) (entry_fact_2) (entry_fact_3) (entry_fact_4) (entry_fact_5) (entry_fact_6) (entry_fact_7) (entry_fact_8) (entry_fact_9) (entry_fact_10) (entry_fact_11) (entry_fact_12) (entry_fact_13) (entry_fact_14) (entry_fact_15) (entry_fact_16) (entry_fact_17) (entry_fact_18) (entry_fact_19)) -∗
 decodeItemSelectedCode -∗
 instr_body 0x800d6a08 (machineAt6a08_322 (args) (returnAddress) (K) (entry_fact_0) (entry_fact_1) (entry_fact_2) (entry_fact_3) (entry_fact_4) (entry_fact_5) (entry_fact_6) (entry_fact_7) (entry_fact_8) (entry_fact_9) (entry_fact_10) (entry_fact_11) (entry_fact_12) (entry_fact_13) (entry_fact_14) (entry_fact_15) (entry_fact_16) (entry_fact_17) (entry_fact_18) (entry_fact_19)).

Proof.
 zesu_block.
Qed.
