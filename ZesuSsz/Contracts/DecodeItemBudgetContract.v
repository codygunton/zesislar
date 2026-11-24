From Coq Require Import ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemChargedSelected.
Require ZesuSsz.Stock.Closure.index_decodeItem.
Open Scope Z_scope.

(* rlp.decodeItem with a step bound (plan Stage T, T7). The model of
   DecodeItemSelected.v (decodeItemSelectedModel), unchanged in its
   arguments, outcome relation, entry and exit resources, with
   - the function's code charged (decodeItemChargedCode): each fetch of one
     of its instructions consumes one step credit;
   - `step_budget decodeItemBudget` owned by the entry: the number of
     instruction fetches from the entry to the return, the entry's own
     instruction included. Both loops of the function (+0xc4, +0x164) read
     the length-of-length bytes of a long string or list, one byte per
     iteration of 5 instructions; the code enters them only with a
     length-of-length in [1, 8], so each loop has at most 8 iterations and
     the budget is a constant: the longest path of the control flow graph
     with each loop cut's potential `5 * (end - cursor) + 12` bounded by 52
     at its entry (`tools/block/budgets.py --function decodeItemBudget`).
   The fetch at the return address belongs to the caller. *)

Notation decodeItemBudget := ((75) : Z) (only parsing).

Definition decodeItemBudgetResources `{!islaG Sigma} `{!threadG}
    (domain : DecodeItemArgs -> Prop) :
    IslarisContractResources DecodeItemArgs DecodeItemOutcome :=
  {| islarisCode := decodeItemChargedCode;
     islarisEntry := fun args =>
       (decodeItemEntryResources domain args ∗ step_budget decodeItemBudget)%I;
     islarisExit := decodeItemExitResources |}.

Definition decodeItemBudgetModel (returnAddress : Z) :
    IslarisContractModel DecodeItemArgs DecodeItemOutcome :=
  {| islarisContractAllows := fun args after =>
       decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
       DecodeMeaningModuloKnownBugs args after;
     islarisContractStep :=
       ZesuSsz.Stock.Closure.index_decodeItem.decodeItem_cfg_step;
     islarisContractResources := fun Sigma HG HT =>
       @decodeItemBudgetResources Sigma HG HT
         (decodeItemDomainAt returnAddress decodeItemC1BDomain) |}.

(* This declaration states the native proof objective. It does not prove it. *)
Definition DecodeItemBudgetContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemBudgetModel returnAddress).
