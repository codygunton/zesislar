Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Finish.
Require Import ZesuSsz.Automation.RawWordArrayWitness.
From Coq Require Import ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Automation.All.
Open Scope Z_scope.
Lemma canonical_constant : (BV 64 2 + BV 64 3)%bv = BV 64 5.
Proof. ZesuSsz.Automation.Finish.zesu_finish_constant. Qed.
Lemma canonical_symbolic (word : bv 64) : word = word.
Proof. Fail ZesuSsz.Automation.Finish.zesu_finish_constant. reflexivity. Qed.
Lemma symbolic_width_refusal (width : N) (word : bv width) : True.
Proof.
 Fail ZesuSsz.Automation.RawWordArrayWitness.zesu_raw_array_check_word word.
 exact I.
Qed.
Print Assumptions canonical_constant.
Print Assumptions canonical_symbolic.
Print Assumptions symbolic_width_refusal.
