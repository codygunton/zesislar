Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemCallSpec.
Require Import ZesuSsz.Contracts.DecodeItemCallSpec2.
Require Import ZesuSsz.Compliance.DecodeItemCallSpec.

(* The template is a spec only in this proof of its correctness; callers use the
   sealed public spec of ZesuSsz/Interfaces/DecodeItem.v. *)
#[local] Instance : LithiumUnfold (@decodeItemCallSpecDefinition) := I.
Global Typeclasses Opaque decodeItemCallSpecDefinition.

(* The template differs from the frozen-core spec only in which identical
   machine_call it names. ZesuSsz/Interfaces/DecodeItemCorrect.v carries this
   proof over to the sealed public spec decodeItemCallSpec2. *)
Lemma decodeItemCallSpecDefinition_eq `{!islaG Sigma} `{!threadG} :
  @decodeItemCallSpecDefinition Sigma _ _ = @decodeItemCallSpec Sigma _ _.
Proof. reflexivity. Qed.

Lemma decodeItemCallSpecDefinition_correct `{!islaG Sigma} `{!threadG} :
  decodeItemSelectedCode -∗ instr_body decodeItemEntry decodeItemCallSpecDefinition.
Proof. rewrite decodeItemCallSpecDefinition_eq. apply decodeItemCallSpec_correct. Qed.
