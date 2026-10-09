Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma decodeItemStorageExtent16Off (storage : list byte)  (Hlength : length storage = 40%nat) : True.
Proof.
  let target := constr:(SimplAnd ((16 + N.to_nat 8 <= length storage)%nat) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The extent registration accepts an unsupported target."
  else exact I.
Qed.

Lemma decodeItemStorageExtent24Off (storage : list byte)  (Hlength : length storage = 40%nat) : True.
Proof.
  let target := constr:(SimplAnd ((24 + N.to_nat 8 <= length storage)%nat) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The extent registration accepts an unsupported target."
  else exact I.
Qed.

Lemma decodeItemStorageExtent32Off (storage : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte) (Hlength : length storage = 40%nat) : True.
Proof.
  let target := constr:(SimplAnd (length (take 32 storage ++ b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: drop 40 storage) = 40%nat) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The extent registration accepts an unsupported target."
  else exact I.
Qed.

Require Import ZesuSsz.Compliance.DecodeItemHints.

Lemma decodeItemStorageExtent16LiteralOn (base : Z) (storage : list byte)
    (Hlength : length storage = 40%nat) : SimplAnd ((16 + N.to_nat 8 <= length storage)%nat) True.
Proof. typeclasses eauto. Qed.

Lemma decodeItemStorageExtent16UnreducedOn (base : Z) (storage : list byte)
    (Hlength : length storage = 40%nat) : SimplAnd ((Z.to_nat (base + 16 - base) + N.to_nat 8 <= length storage)%nat) True.
Proof. typeclasses eauto. Qed.

Lemma decodeItemStorageExtent24LiteralOn (base : Z) (storage : list byte)
    (Hlength : length storage = 40%nat) : SimplAnd ((24 + N.to_nat 8 <= length storage)%nat) True.
Proof. typeclasses eauto. Qed.

Lemma decodeItemStorageExtent24UnreducedOn (base : Z) (storage : list byte)
    (Hlength : length storage = 40%nat) : SimplAnd ((Z.to_nat (base + 24 - base) + N.to_nat 8 <= length storage)%nat) True.
Proof. typeclasses eauto. Qed.

Lemma decodeItemWord32LiteralOn (base : Z) (storage : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
    (Hlength : length storage = 40%nat) : SimplAnd (length (take 32 storage ++ b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: drop 40 storage) = 40%nat) True.
Proof. typeclasses eauto. Qed.

Lemma decodeItemWord32UnreducedOn (base : Z) (storage : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
    (Hlength : length storage = 40%nat) : SimplAnd (length (take (Z.to_nat (base + 32 - base)) storage ++ b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: drop (Z.to_nat (base + 32 - base) + N.to_nat 8) storage) = 40%nat) True.
Proof. typeclasses eauto. Qed.

Definition extentWordSplice (base offset : Z) (before : list byte)
    (b0 b1 b2 b3 b4 b5 b6 b7 : byte) : list byte :=
  take (Z.to_nat (base + offset - base)) before ++
    b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
    drop (Z.to_nat (base + offset - base) + N.to_nat 8) before.

Lemma decodeItemUpdatedExtent16 (base : Z) (storage : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
    (Hlength : length storage = 40%nat) :
  SimplAnd ((Z.to_nat (base + 16 - base) + N.to_nat 8 <= length (extentWordSplice base 8 (extentWordSplice base 0 (extentWordSplice base 32 storage b0 b1 b2 b3 b4 b5 b6 b7) b0 b1 b2 b3 b4 b5 b6 b7) b0 b1 b2 b3 b4 b5 b6 b7))%nat) True.
Proof. unfold extentWordSplice. typeclasses eauto. Qed.

Lemma decodeItemUpdatedExtent24 (base : Z) (storage : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
    (Hlength : length storage = 40%nat) :
  SimplAnd ((Z.to_nat (base + 24 - base) + N.to_nat 8 <= length (extentWordSplice base 16 (extentWordSplice base 8 (extentWordSplice base 0 (extentWordSplice base 32 storage b0 b1 b2 b3 b4 b5 b6 b7) b0 b1 b2 b3 b4 b5 b6 b7) b0 b1 b2 b3 b4 b5 b6 b7) b0 b1 b2 b3 b4 b5 b6 b7))%nat) True.
Proof. unfold extentWordSplice. typeclasses eauto. Qed.

Lemma decodeItemUpdatedExtent24Literal (base : Z) (storage : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
    (Hlength : length storage = 40%nat) :
  SimplAnd ((24 + N.to_nat 8 <= length (extentWordSplice base 16 (extentWordSplice base 8 (extentWordSplice base 0 (extentWordSplice base 32 storage b0 b1 b2 b3 b4 b5 b6 b7) b0 b1 b2 b3 b4 b5 b6 b7) b0 b1 b2 b3 b4 b5 b6 b7) b0 b1 b2 b3 b4 b5 b6 b7))%nat) True.
Proof. unfold extentWordSplice. typeclasses eauto. Qed.

Lemma decodeItemExtent16MissingLength (storage : list byte) : True.
Proof.
  let target := constr:(SimplAnd ((16 + N.to_nat 8 <= length storage)%nat) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The extent registration accepts an unsupported target."
  else exact I.
Qed.

Lemma decodeItemExtent24MissingLength (storage : list byte) : True.
Proof.
  let target := constr:(SimplAnd ((24 + N.to_nat 8 <= length storage)%nat) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The extent registration accepts an unsupported target."
  else exact I.
Qed.

Lemma decodeItemWord32MissingLength (storage : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte) : True.
Proof.
  let target := constr:(SimplAnd (length (take 32 storage ++ b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: drop 40 storage) = 40%nat) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The extent registration accepts an unsupported target."
  else exact I.
Qed.

Lemma decodeItemExtentUnsupportedOffset (storage : list byte) (Hlength : length storage = 40%nat) : True.
Proof.
  let target := constr:(SimplAnd ((20 + N.to_nat 8 <= length storage)%nat) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The extent registration accepts an unsupported target."
  else exact I.
Qed.

Lemma decodeItemExtentUnsupportedWidth (storage : list byte) (Hlength : length storage = 40%nat) : True.
Proof.
  let target := constr:(SimplAnd ((16 + N.to_nat 4 <= length storage)%nat) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The extent registration accepts an unsupported target."
  else exact I.
Qed.

Lemma decodeItemWord32SevenBytes (storage : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte) (Hlength : length storage = 40%nat) : True.
Proof.
  let target := constr:(SimplAnd (length (take 32 storage ++ b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: drop 40 storage) = 40%nat) True) in
  tryif (let instance := constr:(_ : target) in idtac)
  then fail "The extent registration accepts an unsupported target."
  else exact I.
Qed.

Print Assumptions decodeItemStorageExtent16Off.
Print Assumptions decodeItemStorageExtent24Off.
Print Assumptions decodeItemStorageExtent32Off.
Print Assumptions decodeItemStorageExtent16LiteralOn.
Print Assumptions decodeItemStorageExtent16UnreducedOn.
Print Assumptions decodeItemStorageExtent24LiteralOn.
Print Assumptions decodeItemStorageExtent24UnreducedOn.
Print Assumptions decodeItemWord32LiteralOn.
Print Assumptions decodeItemWord32UnreducedOn.
Print Assumptions decodeItemUpdatedExtent16.
Print Assumptions decodeItemUpdatedExtent24.
Print Assumptions decodeItemUpdatedExtent24Literal.
Print Assumptions decodeItemExtent16MissingLength.
Print Assumptions decodeItemExtent24MissingLength.
Print Assumptions decodeItemWord32MissingLength.
Print Assumptions decodeItemExtentUnsupportedOffset.
Print Assumptions decodeItemExtentUnsupportedWidth.
Print Assumptions decodeItemWord32SevenBytes.
