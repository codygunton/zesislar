From Coq Require Import ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuStock.CalleeIdentity.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import InstrSpecs.Lookup.

Definition decodeItemSelectedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_decodeItem.instr_map).

Definition decodeItemSelectedModel (returnAddress : Z) :
    IslarisContractModel DecodeItemArgs DecodeItemOutcome :=
  {| islarisContractAllows := fun args after =>
       decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
       DecodeMeaningModuloKnownBugs args after;
     islarisContractStep :=
       ZesuSsz.Stock.Closure.index_decodeItem.decodeItem_cfg_step;
     islarisContractResources := fun Sigma HG HT =>
       decodeItemResources (decodeItemSelectedCode (Sigma:=Sigma))
         (decodeItemDomainAt returnAddress decodeItemC1BDomain) |}.

Definition DecodeItemSelectedComplianceStatement : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemSelectedModel returnAddress).
