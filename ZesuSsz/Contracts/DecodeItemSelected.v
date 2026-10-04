From Coq Require Import ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuStock.CalleeIdentity.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.

Definition decodeItemSelectedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  ([∗ list] instruction ∈
    ZesuSsz.Stock.Closure.index_decodeItem.instr_map,
    instr instruction.1 (Some instruction.2))%I.

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
