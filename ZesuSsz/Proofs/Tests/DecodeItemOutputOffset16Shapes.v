Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Open Scope Z_scope.

Lemma decodeItemOutputOffset16LiteralOff (args : DecodeItemArgs) : True.
Proof.
  let target := constr:(SimplAnd (Z.of_nat 16 =
    (decodeItemOutputPointer args + 16 - decodeItemOutputPointer args) `div` 1) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The offset16 registration is active before its import."
  else exact I.
Qed.

Lemma decodeItemOutputOffset16UnreducedOff (args : DecodeItemArgs) : True.
Proof.
  let target := constr:(SimplAnd (Z.of_nat 16 =
    (decodeItemOutputPointer args + 16 - decodeItemOutputPointer args) `div` Z.of_N 1) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The unreduced offset16 registration is active before its import."
  else exact I.
Qed.

Require Import ZesuSsz.Compliance.DecodeItemOutputBaseWitnessFacts.

Lemma decodeItemOutputOffset16LiteralOn (args : DecodeItemArgs) :
  SimplAnd (Z.of_nat 16 =
    (decodeItemOutputPointer args + 16 - decodeItemOutputPointer args) `div` 1) True.
Proof. typeclasses eauto. Qed.

Lemma decodeItemOutputOffset16UnreducedOn (args : DecodeItemArgs) :
  SimplAnd (Z.of_nat 16 =
    (decodeItemOutputPointer args + 16 - decodeItemOutputPointer args) `div` Z.of_N 1) True.
Proof. typeclasses eauto. Qed.

Lemma decodeItemOutputOffset16UnsupportedDivisor (args : DecodeItemArgs) : True.
Proof.
  let target := constr:(SimplAnd (Z.of_nat 16 =
    (decodeItemOutputPointer args + 16 - decodeItemOutputPointer args) `div` 2) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The offset16 registration accepts divisor two."
  else exact I.
Qed.

Print Assumptions decodeItemOutputOffset16LiteralOff.
Print Assumptions decodeItemOutputOffset16UnreducedOff.
Print Assumptions decodeItemOutputOffset16LiteralOn.
Print Assumptions decodeItemOutputOffset16UnreducedOn.
Print Assumptions decodeItemOutputOffset16UnsupportedDivisor.
