Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Open Scope Z_scope.

Definition machineReturn6a78_180 `{!islaG Sigma} `{!threadG}
  (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) (entry_fact_0 : (decodeItemReturnAddress ( args ) = ( returnAddress ))%Z) (entry_fact_1 : (( decodeItemInputLength ( args ) ) = Z.of_nat ( List.length ( decodeItemInputBytes ( args ) ) ))%Z) (entry_fact_2 : (List.length ( decodeItemBeforeStorage ( args ) ) = 40)%nat) (entry_fact_3 : (0 <= ( decodeItemInputPointer ( args ) ))%Z) (entry_fact_4 : (0 <= ( decodeItemInputLength ( args ) ))%Z) (entry_fact_5 : (0 <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_6 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_7 : (( decodeItemOutputPointer ( args ) ) + 40 < ( 18446744073709551616 ))%Z) (entry_fact_8 : (( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_9 : (( decodeItemStackPointer ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_10 : (( 2684354560 ) + ( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_11 : (( decodeItemStackPointer ( args ) ) <= ( 3221225472 ))%Z) (entry_fact_12 : (0 <= ( decodeItemReturnAddress ( args ) ))%Z) (entry_fact_13 : (( decodeItemReturnAddress ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_14 : (( decodeItemReturnAddress ( args ) ) mod 4 = 0)%Z) (entry_fact_15 : (( 2684354560 ) <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_16 : (( decodeItemOutputPointer ( args ) ) + 40 <= ( 3221225472 ))%Z) (entry_fact_17 : (0 <= ( decodeItemInputEnd ( args ) ))%Z) (entry_fact_18 : (( decodeItemInputEnd ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_19 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) <= ( decodeItemInputEnd ( args ) ))%Z) : iProp Sigma :=
  ((∃ outcome : DecodeItemOutcome,
      decodeItemExitResourcesRegisters args outcome ∗
      ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
        DecodeMeaningModuloKnownBugs args outcome⌝) ∗ K)%I.
