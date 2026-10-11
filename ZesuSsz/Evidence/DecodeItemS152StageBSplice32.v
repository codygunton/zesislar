Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.

Lemma s152_stageB_splice32 (base : Z) (storage : list (bv 8)) :
 length storage = 40%nat ->
 length (take (Z.to_nat (Z.sub (Z.add base 32) base)) storage ++
 bv_to_little_endian 8 8 4 ++
 drop (Z.to_nat (Z.sub (Z.add base 32) base) + N.to_nat 8) storage) = 40%nat.
Proof.
intros Hstorage.
apply decodeItemOutputWord32Length; [exact Hstorage |].
rewrite length_bv_to_little_endian; lia.
Qed.
