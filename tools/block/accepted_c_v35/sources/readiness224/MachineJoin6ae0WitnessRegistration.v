Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import stdpp.list.
Require Import stdpp.bitvector.definitions.
Require Import iris.algebra.dfrac.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ResultImage.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import lithium.lvar.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Import ListNotations.
Open Scope Z_scope.
Require Import Coq.Strings.String.
Require Import ZesuSsz.Evidence.EntryWitnessInputs.
Require Import ZesuSsz.Evidence.EntryWitnessSelector.
Require Import ZesuSsz.Generated.DecodeItem.MachineJoin6ae0Entries.
Require Import ZesuSsz.Generated.DecodeItem.MachineJoin6ae0SourceOwner.
Local Open Scope string_scope.

Definition generatedJoin6ae0WitnessData (source_words : (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * unit)%type)%type)%type)%type)%type)%type)
  : (bv 64 * (bv 64 * (bv 64 * (bv 64 * (bv 64 * (bv 64 * unit)%type)%type)%type)%type)%type)%type :=
  (((fst source_words)), (((fst (snd source_words))), (((fst (snd (snd source_words)))), (((fst (snd (snd (snd source_words))))), (((fst (snd (snd (snd (snd source_words)))))), (((fst (snd (snd (snd (snd (snd source_words))))))), tt)))))).

#[export] Instance generatedJoin6ae0_witness_mapping `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (domain : DecodeItemArgs -> Prop) :
  ZesuSsz.Evidence.EntryWitnessInputs.ZesuEntryWitnessMapping (ZesuSsz.Generated.DecodeItem.MachineJoin6ae0Entries.generatedJoin6ae0 (args) (returnAddress) (domain)) ((bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * unit)%type)%type)%type)%type)%type)%type) (bv 64 * (bv 64 * (bv 64 * (bv 64 * (bv 64 * (bv 64 * unit)%type)%type)%type)%type)%type)%type :=
  {| zesu_witness_input := (ZesuWitnessPair (ZesuWitnessRegister 64%N "x11") (ZesuWitnessPair (ZesuWitnessRegister 64%N "x12") (ZesuWitnessPair (ZesuWitnessRegister 64%N "x13") (ZesuWitnessPair (ZesuWitnessRegister 64%N "x14") (ZesuWitnessPair (ZesuWitnessRegister 64%N "x15") (ZesuWitnessPair (ZesuWitnessRegister 64%N "x16") ZesuWitnessUnit))))));
     zesu_witness_mapping := generatedJoin6ae0WitnessData |}.
