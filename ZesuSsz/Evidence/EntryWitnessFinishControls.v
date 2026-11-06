Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.EntryWitnessFinish.
From Coq Require Import ZArith Lia.
From stdpp Require Import bitvector.tactics.
Require Import ZesuSsz.Automation.All.
Local Open Scope Z_scope.
Lemma byte_bias_scalar232 (word : bv 8) :
  184 <= bv_unsigned word <= 191 ->
  (bv_and (bv_and (bv_sign_extend 64 word) (BV 64 255) + BV 64 73) (BV 64 255) + BV 64 1)%bv =
  Z_to_bv 64 (bv_unsigned word - 183 + 1).
Proof. intros [Hlower Hupper]. EntryWitnessFinish.zesu_byte_bias_finish. Qed.
Lemma byte_bias_pointer232 (word : bv 8) (pointer : Z) :
  184 <= bv_unsigned word <= 191 ->
  (Z_to_bv 64 pointer +
   (bv_and (bv_and (bv_sign_extend 64 word) (BV 64 255) + BV 64 73) (BV 64 255) + BV 64 1))%bv =
  Z_to_bv 64 (pointer + 1 + (bv_unsigned word - 183)).
Proof. intros [Hlower Hupper]. EntryWitnessFinish.zesu_byte_bias_finish. Qed.
Lemma byte_bias_missing_range_refuses232 (word : bv 8) : True.
Proof.
 Fail assert ((bv_and (bv_and (bv_sign_extend 64 word) (BV 64 255) + BV 64 73) (BV 64 255) + BV 64 1)%bv =
   Z_to_bv 64 (bv_unsigned word - 183 + 1)) by EntryWitnessFinish.zesu_byte_bias_finish.
 exact I.
Qed.
Lemma byte_bias_symbolic_offset_refuses232 (word : bv 8) (offset : bv 64) : True.
Proof.
 Fail assert ((bv_and (bv_and (bv_sign_extend 64 word) (BV 64 255) + offset) (BV 64 255) + BV 64 1)%bv =
   Z_to_bv 64 (bv_unsigned word - 183 + 1)) by EntryWitnessFinish.zesu_byte_bias_finish.
 exact I.
Qed.
Lemma byte_bias_unrelated_refuses232 : True.
Proof. Fail EntryWitnessFinish.zesu_byte_bias_finish. exact I. Qed.
Lemma entry_finish_missing_marker_refuses232 : True.
Proof. Fail EntryWitnessFinish.zesu_entry_witness_finish ltac:(idtac) ltac:(idtac). exact I. Qed.
Lemma entry_finish_exhausted_phase_refuses232 : True.
Proof. Fail EntryWitnessFinish.zesu_entry_finish_phase O ltac:(idtac). exact I. Qed.

Lemma byte_bias_nonwrap_refuses233 (word : bv 8) :
  0 <= bv_unsigned word <= 1 -> True.
Proof.
 intros Hrange.
 Fail assert ((bv_and (bv_and (bv_sign_extend 64 word) (BV 64 255) + BV 64 73) (BV 64 255) + BV 64 1)%bv =
   Z_to_bv 64 (bv_unsigned word - 183 + 1)) by EntryWitnessFinish.zesu_byte_bias_finish.
 exact I.
Qed.
Lemma byte_bias_wrong_mask_refuses233 (word : bv 8) : True.
Proof.
 Fail assert ((bv_and (bv_and (bv_sign_extend 64 word) (BV 64 127) + BV 64 73) (BV 64 127) + BV 64 1)%bv =
   Z_to_bv 64 (bv_unsigned word - 183 + 1)) by EntryWitnessFinish.zesu_byte_bias_finish.
 exact I.
Qed.
Lemma byte_bias_unresolved_refuses233 : True.
Proof.
 Fail let word := open_constr:(_ : bv 8) in
 assert ((bv_and (bv_and (bv_sign_extend 64 word) (BV 64 255) + BV 64 73) (BV 64 255) + BV 64 1)%bv =
   Z_to_bv 64 (bv_unsigned word - 183 + 1)) by EntryWitnessFinish.zesu_byte_bias_finish.
 exact I.
Qed.
