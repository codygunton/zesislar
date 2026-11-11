Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The closing fact is an Iris pure hypothesis. The finisher calls see the
   pure goal after `iPureIntro`, without it; the fact enters the context only
   when the package route opens the resource groups and splits the conjunct
   off. *)
Lemma package_split_masked_bound `{!islaG Sigma} `{!threadG} (a c : Z) (R : iProp Sigma) :
  ⌜¬ (c >= bv_unsigned (bv_and (Z_to_bv 64 a) (BV 64 63)))⌝ ∗ R -∗
  R ∗ ⌜c < bv_unsigned (bv_and (Z_to_bv 64 a) (BV 64 63))⌝.
Proof. zesu_block2. Qed.
