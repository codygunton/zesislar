Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.

Import ListNotations.

Lemma reg_col_exact_bv_to_bits_test `{!islaG Sigma} `{!threadG}
    (left right : bv 64) :
  reg_col
    [(KindReg "x8", ExactShape (RVal_Bits left));
     (KindReg "x9", ExactShape (RVal_Bits right))] -∗
  reg_col
    [(KindReg "x8", BitsShape 64);
     (KindReg "x9", BitsShape 64)].
Proof.
  iIntros "Hregs".
  iApply (reg_col_exact_bv_to_bits ["x8"; "x9"] [left; right]);
    [reflexivity | iExact "Hregs"].
Qed.
