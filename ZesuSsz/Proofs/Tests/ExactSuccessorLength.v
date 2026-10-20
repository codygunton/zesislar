Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import isla.riscv64.riscv64.
From Coq Require Import List Lia.

Lemma exact_successor_length (outputBytes : list (bv 8))
    (Hlength : length outputBytes = 40%nat) :
  (Nat.min 24 (length outputBytes) + S (S (S (S (S (S (S (S (length (drop (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (N.to_nat 8%N))))))))))))))))))))))))) (<[16:=BV 8 0]> outputBytes)))))))))))%nat = 40%nat.
Proof.
  zesu_finish_contract_arithmetic.
Qed.

Lemma exact_successor_wrong_total (outputBytes : list (bv 8))
    (Hlength : length outputBytes = 40%nat) : True.
Proof.
  Fail assert (Hwrong : (Nat.min 24 (length outputBytes) + S (S (S (S (S (S (S (S (length (drop (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (N.to_nat 8%N))))))))))))))))))))))))) (<[16:=BV 8 0]> outputBytes)))))))))))%nat = 41%nat) by zesu_finish_contract_arithmetic.
  exact I.
Qed.

Print Assumptions exact_successor_length.
Print Assumptions exact_successor_wrong_total.

