Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.AltFlFreeBlockEntries.
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Lemma freeSizeClassLeaf0 (size : Z) :
  0 <= size <= 8 -> freeSizeClassOfBytes size = 0.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf1 (size : Z) :
  9 <= size <= 16 -> freeSizeClassOfBytes size = 1.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf2 (size : Z) :
  17 <= size <= 32 -> freeSizeClassOfBytes size = 2.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf3 (size : Z) :
  33 <= size <= 64 -> freeSizeClassOfBytes size = 3.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf4 (size : Z) :
  65 <= size <= 128 -> freeSizeClassOfBytes size = 4.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf5 (size : Z) :
  129 <= size <= 256 -> freeSizeClassOfBytes size = 5.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf6 (size : Z) :
  257 <= size <= 512 -> freeSizeClassOfBytes size = 6.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf7 (size : Z) :
  513 <= size <= 1024 -> freeSizeClassOfBytes size = 7.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf8 (size : Z) :
  1025 <= size <= 2048 -> freeSizeClassOfBytes size = 8.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf9 (size : Z) :
  2049 <= size <= 4096 -> freeSizeClassOfBytes size = 9.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf10 (size : Z) :
  4097 <= size <= 8192 -> freeSizeClassOfBytes size = 10.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf11 (size : Z) :
  8193 <= size <= 16384 -> freeSizeClassOfBytes size = 11.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf12 (size : Z) :
  16385 <= size <= 32768 -> freeSizeClassOfBytes size = 12.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf13 (size : Z) :
  32769 <= size <= 65536 -> freeSizeClassOfBytes size = 13.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf14 (size : Z) :
  65537 <= size <= 131072 -> freeSizeClassOfBytes size = 14.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf15 (size : Z) :
  131073 <= size <= 262144 -> freeSizeClassOfBytes size = 15.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf16 (size : Z) :
  262145 <= size <= 524288 -> freeSizeClassOfBytes size = 16.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf17 (size : Z) :
  524289 <= size <= 1048576 -> freeSizeClassOfBytes size = 17.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf18 (size : Z) :
  1048577 <= size <= 2097152 -> freeSizeClassOfBytes size = 18.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf19 (size : Z) :
  2097153 <= size <= 4194304 -> freeSizeClassOfBytes size = 19.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.

Lemma freeSizeClassLeaf20 (size : Z) :
  4194305 <= size <= 8388608 -> freeSizeClassOfBytes size = 20.
Proof.
intros Hrange.
unfold freeSizeClassOfBytes.
repeat match goal with
| |- context [Z.leb ?left ?right] => destruct (Z.leb_spec left right)
end; lia.
Qed.
