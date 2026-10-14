Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Open Scope Z_scope.

Lemma decodeItemOutputOffset8RegistrationOff (args : DecodeItemArgs) : True.
Proof.
  let target := constr:(SimplAnd (Z.of_nat 8 =
    decodeItemOutputPointer args + 8 - decodeItemOutputPointer args) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The offset8 registration is active before its import."
  else exact I.
Qed.

Require Import ZesuSsz.Compliance.DecodeItemOutputBaseWitnessFacts.

Lemma decodeItemOutputOffset8RegistrationOn (args : DecodeItemArgs) :
  SimplAnd (Z.of_nat 8 =
    decodeItemOutputPointer args + 8 - decodeItemOutputPointer args) True.
Proof. typeclasses eauto. Qed.

Print Assumptions decodeItemOutputOffset8RegistrationOff.
Print Assumptions decodeItemOutputOffset8RegistrationOn.
