Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.v1.
Require Import ZesuSsz.Automation.Approved.
Require Import isla.isla.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.MachineSlice6960Entries.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Generated.DecodeItem.MachineSlice6960StructuralRegistrations.
Require Import ZesuSsz.Generated.DecodeItem.MachineBranch198Structural.
Require Import ZesuSsz.Generated.DecodeItem.PilotA201Structural.
Require Import ZesuSsz.Generated.DecodeItem.MachineBranch198Entries.
Require Import ZesuSsz.Generated.DecodeItem.PilotA201Entries.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation.EffectiveOverrides.

Definition DesignedEntry_800d6974
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) (entry_fact_0 : ( decodeItemReturnAddress ( args ) = ( returnAddress ) ) % Z) (entry_fact_1 : ( ( decodeItemInputLength ( args ) ) = Z . of_nat ( List . length ( decodeItemInputBytes ( args ) ) ) ) % Z) (entry_fact_2 : ( List . length ( decodeItemBeforeStorage ( args ) ) = 40 ) % nat) (entry_fact_3 : ( 0 < = ( decodeItemInputPointer ( args ) ) ) % Z) (entry_fact_4 : ( 0 < = ( decodeItemInputLength ( args ) ) ) % Z) (entry_fact_5 : ( 0 < = ( decodeItemOutputPointer ( args ) ) ) % Z) (entry_fact_6 : ( ( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) < ( 18446744073709551616 ) ) % Z) (entry_fact_7 : ( ( decodeItemOutputPointer ( args ) ) + 40 < ( 18446744073709551616 ) ) % Z) (entry_fact_8 : ( ( 16 ) < = ( decodeItemStackPointer ( args ) ) ) % Z) (entry_fact_9 : ( ( decodeItemStackPointer ( args ) ) < ( 18446744073709551616 ) ) % Z) (entry_fact_10 : ( ( 2684354560 ) + ( 16 ) < = ( decodeItemStackPointer ( args ) ) ) % Z) (entry_fact_11 : ( ( decodeItemStackPointer ( args ) ) < = ( 3221225472 ) ) % Z) (entry_fact_12 : ( 0 < = ( decodeItemReturnAddress ( args ) ) ) % Z) (entry_fact_13 : ( ( decodeItemReturnAddress ( args ) ) < ( 18446744073709551616 ) ) % Z) (entry_fact_14 : ( ( decodeItemReturnAddress ( args ) ) mod 4 = 0 ) % Z) (entry_fact_15 : ( ( 2684354560 ) < = ( decodeItemOutputPointer ( args ) ) ) % Z) (entry_fact_16 : ( ( decodeItemOutputPointer ( args ) ) + 40 < = ( 3221225472 ) ) % Z) (entry_fact_17 : ( 0 < = ( decodeItemInputEnd ( args ) ) ) % Z) (entry_fact_18 : ( ( decodeItemInputEnd ( args ) ) < ( 18446744073709551616 ) ) % Z) (entry_fact_19 : ( ( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) < = ( decodeItemInputEnd ( args ) ) ) % Z) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.MachineSlice6960Entries.machineAt6974 (args) (returnAddress) (K) (entry_fact_0) (entry_fact_1) (entry_fact_2) (entry_fact_3) (entry_fact_4) (entry_fact_5) (entry_fact_6) (entry_fact_7) (entry_fact_8) (entry_fact_9) (entry_fact_10) (entry_fact_11) (entry_fact_12) (entry_fact_13) (entry_fact_14) (entry_fact_15) (entry_fact_16) (entry_fact_17) (entry_fact_18) (entry_fact_19)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6974) := I.
Global Typeclasses Opaque DesignedEntry_800d6974.

Lemma DesignedBoundary_800d6974 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) (entry_fact_0 : ( decodeItemReturnAddress ( args ) = ( returnAddress ) ) % Z) (entry_fact_1 : ( ( decodeItemInputLength ( args ) ) = Z . of_nat ( List . length ( decodeItemInputBytes ( args ) ) ) ) % Z) (entry_fact_2 : ( List . length ( decodeItemBeforeStorage ( args ) ) = 40 ) % nat) (entry_fact_3 : ( 0 < = ( decodeItemInputPointer ( args ) ) ) % Z) (entry_fact_4 : ( 0 < = ( decodeItemInputLength ( args ) ) ) % Z) (entry_fact_5 : ( 0 < = ( decodeItemOutputPointer ( args ) ) ) % Z) (entry_fact_6 : ( ( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) < ( 18446744073709551616 ) ) % Z) (entry_fact_7 : ( ( decodeItemOutputPointer ( args ) ) + 40 < ( 18446744073709551616 ) ) % Z) (entry_fact_8 : ( ( 16 ) < = ( decodeItemStackPointer ( args ) ) ) % Z) (entry_fact_9 : ( ( decodeItemStackPointer ( args ) ) < ( 18446744073709551616 ) ) % Z) (entry_fact_10 : ( ( 2684354560 ) + ( 16 ) < = ( decodeItemStackPointer ( args ) ) ) % Z) (entry_fact_11 : ( ( decodeItemStackPointer ( args ) ) < = ( 3221225472 ) ) % Z) (entry_fact_12 : ( 0 < = ( decodeItemReturnAddress ( args ) ) ) % Z) (entry_fact_13 : ( ( decodeItemReturnAddress ( args ) ) < ( 18446744073709551616 ) ) % Z) (entry_fact_14 : ( ( decodeItemReturnAddress ( args ) ) mod 4 = 0 ) % Z) (entry_fact_15 : ( ( 2684354560 ) < = ( decodeItemOutputPointer ( args ) ) ) % Z) (entry_fact_16 : ( ( decodeItemOutputPointer ( args ) ) + 40 < = ( 3221225472 ) ) % Z) (entry_fact_17 : ( 0 < = ( decodeItemInputEnd ( args ) ) ) % Z) (entry_fact_18 : ( ( decodeItemInputEnd ( args ) ) < ( 18446744073709551616 ) ) % Z) (entry_fact_19 : ( ( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) < = ( decodeItemInputEnd ( args ) ) ) % Z)   :
  instr_pre 0x800d697c (ZesuSsz.Generated.DecodeItem.PilotA201Entries.machineAt697c_201 (args) (returnAddress) (K) (entry_fact_0) (entry_fact_1) (entry_fact_2) (entry_fact_3) (entry_fact_4) (entry_fact_5) (entry_fact_6) (entry_fact_7) (entry_fact_8) (entry_fact_9) (entry_fact_10) (entry_fact_11) (entry_fact_12) (entry_fact_13) (entry_fact_14) (entry_fact_15) (entry_fact_16) (entry_fact_17) (entry_fact_18) (entry_fact_19))%I -∗
  instr_pre 0x800d69a4 (ZesuSsz.Generated.DecodeItem.MachineBranch198Entries.machineAt69a4_198 (args) (returnAddress) (K) (entry_fact_0) (entry_fact_1) (entry_fact_2) (entry_fact_3) (entry_fact_4) (entry_fact_5) (entry_fact_6) (entry_fact_7) (entry_fact_8) (entry_fact_9) (entry_fact_10) (entry_fact_11) (entry_fact_12) (entry_fact_13) (entry_fact_14) (entry_fact_15) (entry_fact_16) (entry_fact_17) (entry_fact_18) (entry_fact_19))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6974
    (DesignedEntry_800d6974 args returnAddress K entry_fact_0 entry_fact_1 entry_fact_2 entry_fact_3 entry_fact_4 entry_fact_5 entry_fact_6 entry_fact_7 entry_fact_8 entry_fact_9 entry_fact_10 entry_fact_11 entry_fact_12 entry_fact_13 entry_fact_14 entry_fact_15 entry_fact_16 entry_fact_17 entry_fact_18 entry_fact_19).
Proof.
  zesu_block.
Qed.

Print Assumptions DesignedBoundary_800d6974.
