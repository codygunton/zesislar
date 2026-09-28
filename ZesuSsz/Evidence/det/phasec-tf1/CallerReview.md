# TF1 caller junction draft

The draft preserves the original caller resources.
The prepared view has eight outer conjuncts, including `True`.
The view exposes one two-word array at `sp+920`.
The view exposes one eight-word array at `sp+936`.
The view exposes one seven-word array at `sp+16`.
The view exposes the original 32-byte scratch region at `sp-80`.
The first payload and the active payload bundle remain separate.
One opaque bundle owns all untouched resources.
That bundle has no `LithiumUnfold` instance.

The source prefix covers `sp+312` through `sp+919`.
The source suffix covers `sp+1000` through `sp+1031`.
The source arrays partition the same original 720 bytes.
The copied array covers `sp+16` through `sp+71`.
The copied remainder retains the other original copied words.
The inactive payload bundle owns no active payload resource.
The prepared view does not retain a second full source array.
The reverse equivalence restores the original source, copied words, and payload resources.
This is resource reassembly. The machine exit proof remains open.

The final equivalence uses three hand lines.
The conditional equivalence uses four hand lines.
The initial descriptor conversion uses five hand lines.
The facts proofs use at most three hand lines.
MCP checked the proofs after the bundle became opaque.
MCP compiled the opaque version. `Print Assumptions tail_fields_caller_junction` returned `Closed under the global context`.
MCP verification passed with `assumptions: []`.
No consumer changed for this draft.
The draft imports these exact dependencies:

- `Require Import ZesuSsz.Automation.All.`
- `Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsSourceJunction.`
- `Require Import ZesuSsz.Automation.ArraySlices.`
- `Require Import ZesuSsz.Contracts.IslarisMemory.`
- `Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.`
- `Require Import ZesuSsz.Contracts.Endpoints.`
- `Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.`
- `Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.`
- `Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderValueTransactions.`
- `From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessRepresentation WriteSuccessExactValueSpec WriteSuccessValueBlock WriteSuccessByteLists WriteSuccessTransactionsSpec WriteSuccessTransactionsPost15674Boundary.`
- `Require Import isla.riscv64.riscv64.`
- `From Coq Require Import Lists.List.`
- `Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsPayloadJunction.`
- `Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsCopiedJunction.`
- `Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.`
- `Require Import ZesuSsz.Automation.PackedWordValues.`

The original caller and machine exit statements remain unchanged.
No consumer changed yet.
